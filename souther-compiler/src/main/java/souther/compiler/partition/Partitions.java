package souther.compiler.partition;

import souther.compiler.ast.Ast;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.codegen.InvariantConstraints;
import souther.compiler.diag.SourceRef;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * The equivalence classes a model already states, read off the types a behavior takes.
 *
 * <p>A type's cases are the classes; a threshold in an invariant is where one class ends and the next
 * begins. Nothing is invented: a position the model draws no line through has no classes, and is
 * reported as not derivable. An {@code Int} with no invariant is not silently split at zero, because
 * that would measure coverage of a rule the model never stated and report a gap for failing to test it.
 */
public final class Partitions {

    /** How deep a product is taken apart. Two levels reach a field of a record a parameter holds,
     * which is where domain rules are written; below that a report stops being about anything the
     * author would recognise as one input. */
    static final int MAX_DEPTH = 2;

    /** How many axes one behavior is measured at. Past this the pairs are more than a person reads. */
    static final int MAX_AXES = 12;

    /**
     * A position dropped for being past the limit, and what dropping it cost.
     *
     * <p>The two are not the same loss. An axis with a cut in it was carrying boundaries some rule
     * drew, and nothing can ask about them now — what the rows cover there is unknown rather than
     * complete. An axis with only classes was carrying a measure nothing refuses a build over, so
     * losing it costs a line in a report and no more. Recorded here because the difference cannot be
     * read back afterwards: neither leaves a boundary behind, and a position nobody measured looks
     * exactly like one the rows cover.
     *
     * @param reason              what to say about it, which is the same either way
     * @param carriedAnObligation whether a rule had drawn a line on this position
     */
    public record OmittedAxis(Incompleteness reason, boolean carriedAnObligation) {}

    /**
     * @param axes    the positions this behavior is measured at, in parameter order
     * @param omitted axes past {@link #MAX_AXES}, dropped rather than merged: an axis whose path
     *                nobody can name is not an axis, and folding several into one would put a class
     *                nothing can classify into the denominator
     */
    public record Partitioning(List<Axis> axes, List<OmittedAxis> omitted) {
        public Partitioning {
            axes = List.copyOf(axes);
            omitted = List.copyOf(omitted);
        }

        /** Only the positions the model actually divides. */
        public List<Axis> derivable() {
            return axes.stream().filter(Axis::derivable).toList();
        }
    }

    /** The axes of one behavior. {@code sig} says the types; {@code behavior} says the parameter names,
     * which is what a path is written from. */
    public static Partitioning of(Ast.SpecBehavior behavior, Sig sig, Symbols symbols,
                                  Exclusions excluded) {
        List<Axis> found = new ArrayList<>();
        for (int i = 0; i < sig.ins().size() && i < behavior.params().size(); i++) {
            walk(behavior.name(), TermPath.of(behavior.params().get(i).name()), sig.ins().get(i),
                    0, symbols, found);
        }
        found.replaceAll(axis -> axis.excluding(
                excluded.at(axis.path()).stream().map(TypeName::name).toList()));
        List<Axis> kept = new ArrayList<>();
        List<OmittedAxis> omitted = new ArrayList<>();
        int measured = 0;
        for (Axis axis : found) {
            if (!axis.measurable()) {
                kept.add(axis);   // kept so a report can name what it could not measure
            } else if (measured < MAX_AXES) {
                kept.add(axis);
                measured++;
            } else {
                // Whether this one was carrying an obligation is decided here and not later. A cut is
                // where a boundary comes from, and an axis dropped before `withThresholds` never gets
                // the ones a `guard` would have drawn — so what it has now is what it had. A position
                // that could take a threshold and has no cut yet is not measurable at all and is kept;
                // one with classes and no cuts is a sum or a `Bool`, which no comparison divides.
                omitted.add(new OmittedAxis(Incompleteness.of(Incompleteness.Code.AXIS_OMITTED,
                        Incompleteness.Scope.POSITION, axis.id().toString()),
                        !axis.cuts().isEmpty()));
            }
        }
        return new Partitioning(kept, omitted);
    }

    /**
     * The same axes, with what the behavior's own comparisons divide them into.
     *
     * <p>This is where a numeric position stops being one undivided range. A type's invariant bounds
     * what can exist; a {@code guard} says where the behavior does something else, and both sides of
     * that line hold values a row can write. The cuts merge into one partition and the origins stay
     * apart, so reaching the line through one rule still leaves the others unmet.
     */
    public static Partitioning withThresholds(Partitioning base, List<Threshold> thresholds,
                                              Symbols symbols) {
        List<Axis> out = new ArrayList<>();
        for (Axis axis : base.axes()) {
            List<Threshold> here = thresholds.stream()
                    .filter(t -> t.path().toString().equals(axis.path().toString())).toList();
            if (here.isEmpty()) {
                out.add(axis);
                continue;
            }
            Bounds domain = boundsOf(axis.type(), symbols);
            BigDecimal min = domain == null ? null : domain.min();
            BigDecimal max = domain == null ? null : domain.max();
            List<PartitionClass> classes = Intervals.classesOf(
                    Intervals.of(here, min, max), axis.path(), axis.type(), symbols);
            // What the position is, not what an invariant said about it. There is a bound to read
            // only where the type is a newtype carrying one, and a plain `Decimal` has none — read
            // off the bound, every such position would be called an integer and a threshold of
            // `0.5m` would be asked for its exact `long`.
            boolean decimal = TypeOps.base(axis.type(), symbols) == Type.DECIMAL;
            // Through `excluding`, so that a class list replaced by the intervals a threshold cuts
            // keeps only the exclusions it still has classes for.
            out.add(new Axis(axis.id(), axis.path(), axis.type(),
                    classes.isEmpty() ? axis.classes() : classes,
                    merged(axis.cuts(), here, decimal)).excluding(axis.excluded()));
        }
        return new Partitioning(out, base.omitted());
    }

    /** The cuts a position has, with a rule that drew one already there recorded rather than repeated:
     * an invariant and a guard that state the same bound are one cut and two obligations. */
    private static List<Cut> merged(List<Cut> had, List<Threshold> thresholds, boolean decimal) {
        Map<String, Cut> byValue = new LinkedHashMap<>();
        for (Cut cut : had) {
            byValue.put(same(cut.value()), cut);
        }
        for (Threshold each : thresholds) {
            ObservedValue value = numeric(each.value(), decimal);
            byValue.merge(same(value), Cut.at(value, each.origin()),
                    (there, _) -> there.and(each.origin()));
        }
        return List.copyOf(byValue.values());
    }

    /**
     * What makes two cuts one cut: the number, not how it was written.
     *
     * <p>`+invariant value >= 0.00+` and `+guard x <= 0m+` draw one line. Keyed by the value's own
     * spelling they are two, and then a position has two classes both holding zero — which is not a
     * partition, and the classifier that reads a row against it has no answer — and one boundary is
     * owed twice under one printed number.
     */
    private static String same(ObservedValue value) {
        return value instanceof ObservedValue.Decimal d
                ? "d" + d.value().stripTrailingZeros().toPlainString() : String.valueOf(value);
    }

    /**
     * The values a row has to be written at, one per rule that drew a cut.
     *
     * <p>An invariant's bound is met by writing the value: outside it nothing can be constructed, so
     * the edge is the only row there is to write. A guard's line has values on both sides, so it wants
     * the value and its neighbour — and the neighbour only where the type has one to give.
     */
    public static List<BoundaryObligation> obligationsOf(Axis axis, Symbols symbols) {
        boolean decimal = TypeOps.base(axis.type(), symbols) == Type.DECIMAL;
        BoundaryDomain domain = decimal ? BoundaryDomain.DECIMAL : BoundaryDomain.INT;
        List<BoundaryObligation> out = new ArrayList<>();
        for (Cut cut : axis.cuts()) {
            for (OriginRef origin : cut.origins()) {
                out.add(new BoundaryObligation(axis.id(), origin,
                        BoundaryObligation.BoundarySide.AT, cut.value()));
                if (origin instanceof OriginRef.GuardOrigin guard) {
                    // The other class's edge is the neighbour on the side the cut value is not on.
                    if (guard.valueBelongsBelow()) {
                        domain.successor(cut.value()).ifPresent(next -> out.add(new BoundaryObligation(
                                axis.id(), origin, BoundaryObligation.BoundarySide.ABOVE, next)));
                    } else {
                        domain.predecessor(cut.value()).ifPresent(before ->
                                out.add(new BoundaryObligation(axis.id(), origin,
                                        BoundaryObligation.BoundarySide.BELOW, before)));
                    }
                }
            }
        }
        return List.copyOf(out);
    }

    /** One position: measured where the model divides it or bounds it, taken apart where it is a
     * record, and recorded as not derivable where it is neither. */
    private static void walk(String behavior, TermPath path, Type type, int depth, Symbols symbols,
                             List<Axis> out) {
        AxisId id = AxisId.of(behavior, path);
        List<PartitionClass> classes = classesOf(type, symbols);
        List<Cut> cuts = cutsOf(type, symbols);
        if (!classes.isEmpty() || !cuts.isEmpty()) {
            out.add(new Axis(id, path, type, classes, cuts));
            return;
        }
        Map<String, Type> fields = productFields(type, symbols);
        if (!fields.isEmpty() && depth < MAX_DEPTH) {
            for (Map.Entry<String, Type> field : fields.entrySet()) {
                walk(behavior, path.then(field.getKey()), field.getValue(), depth + 1, symbols, out);
            }
            return;
        }
        out.add(Axis.notDerivable(id, path, type));
    }

    /** A record's fields, or nothing where the type is not one. A newtype is not taken apart: its
     * {@code value} is the same position it is. */
    private static Map<String, Type> productFields(Type type, Symbols symbols) {
        if (type instanceof Type.Ref ref && symbols.get(ref.name()) instanceof Ast.Data data
                && !data.newtype()) {
            return TypeOps.fieldTypes(data, symbols);
        }
        return Map.of();
    }

    // --- what a type divides its values into ------------------------------------------------------

    static List<PartitionClass> classesOf(Type type, Symbols symbols) {
        if (type == Type.BOOL) {
            return List.of(
                    PartitionClass.of("true", "true", v -> isBool(v, true),
                            RepresentativeSource.of(FixtureTemplate.bool(true))),
                    PartitionClass.of("false", "false", v -> isBool(v, false),
                            RepresentativeSource.of(FixtureTemplate.bool(false))));
        }
        if (type instanceof Type.OptionOf option) {
            List<FixtureTemplate> some = representativesOf(option.element(), symbols);
            return List.of(
                    PartitionClass.of("None", "None", v -> v instanceof ObservedValue.Absent,
                            RepresentativeSource.of(FixtureTemplate.none())),
                    some.isEmpty()
                            ? PartitionClass.ungeneratable("Some", "Some",
                                    v -> !(v instanceof ObservedValue.Absent),
                                    "no value of " + option.element() + " can be written")
                            : PartitionClass.of("Some", "Some",
                                    v -> !(v instanceof ObservedValue.Absent), () -> some));
        }
        if (TypeOps.isSumType(type, symbols)) {
            List<PartitionClass> cases = new ArrayList<>();
            for (TypeName leaf : TypeOps.leafCases(type, symbols)) {
                cases.add(caseClass(leaf, symbols));
            }
            return cases;
        }
        // A numeric newtype's invariant does not divide the values a row can write. Everything outside
        // it is refused at construction (E1903), so there is no class on the other side to cover — the
        // bound leaves a boundary to reach, not a partition to fill. What does divide the values a row
        // can write is a threshold a behavior compares against, which is read from the body.
        return List.of();
    }

    private static PartitionClass caseClass(TypeName leaf, Symbols symbols) {
        Classifier is = v -> switch (v) {
            case ObservedValue.Unit u -> leaf.equals(u.type());
            case ObservedValue.Constructed c -> leaf.equals(c.type());
            case null, default -> false;
        };
        if (!(symbols.get(leaf) instanceof Ast.Data data)) {
            return PartitionClass.of(leaf.name(), leaf.name(), is,
                    RepresentativeSource.of(FixtureTemplate.unitCase(leaf)));   // naming it builds it
        }
        if (data.newtype()) {
            List<FixtureTemplate> inner = insideTheNewtype(leaf, symbols);
            return inner.isEmpty()
                    ? PartitionClass.ungeneratable(leaf.name(), leaf.name(), is,
                            "no value of what `" + leaf.name() + "` wraps can be written")
                    : PartitionClass.of(leaf.name(), leaf.name(), is,
                            () -> inner.stream().map(t -> FixtureTemplate.newtype(leaf, t)).toList());
        }
        // A record case is written field by field, which is the generator's composition and not a
        // value this position can hand over on its own.
        return PartitionClass.ungeneratable(leaf.name(), leaf.name(), is,
                "`" + leaf.name() + "` is a record, whose fields are composed rather than named here");
    }

    // --- reading an invariant's bounds -------------------------------------------------------------

    /** What a newtype's invariant says about the range of its value. */
    private record Bounds(BigDecimal min, BigDecimal max, boolean decimal) {

        boolean isEmpty() {
            return min == null && max == null;
        }

    }

    private static Bounds boundsOf(Type type, Symbols symbols) {
        if (!(type instanceof Type.Ref ref) || !(symbols.get(ref.name()) instanceof Ast.Data data)
                || !data.newtype()) {
            return null;
        }
        Type base = TypeOps.newtypeInner(ref.name(), symbols);
        if (base != Type.INT && base != Type.DECIMAL) {
            return null;
        }
        boolean decimal = base == Type.DECIMAL;
        BigDecimal min = null;
        BigDecimal max = null;
        for (Ast.InvariantClause clause : TypeOps.effectiveInvariants(data, symbols)) {
            for (Ast.Expr each : InvariantConstraints.clauses(clause.expr())) {
                Optional<InvariantConstraints.Constraint> read =
                        InvariantConstraints.of(each, base);
                if (read.isEmpty()) {
                    continue;
                }
                switch (read.get()) {
                    case InvariantConstraints.Min m -> min = highest(min, BigDecimal.valueOf(m.n()));
                    case InvariantConstraints.Max m -> max = lowest(max, BigDecimal.valueOf(m.n()));
                    case InvariantConstraints.Positive _ -> min = highest(min, BigDecimal.ONE);
                    case InvariantConstraints.NonNegative _ -> min = highest(min, BigDecimal.ZERO);
                    case InvariantConstraints.DecimalMin m -> min = highest(min, m.n());
                    case InvariantConstraints.DecimalMax m -> max = lowest(max, m.n());
                    case InvariantConstraints.DecimalPositive _ -> min = highest(min, BigDecimal.ONE);
                    case InvariantConstraints.DecimalNonNegative _ ->
                            min = highest(min, BigDecimal.ZERO);
                    default -> { }   // a rule this partition does not read: length, pattern, size
                }
            }
        }
        return new Bounds(min, max, decimal);
    }

    /** The cuts of a position, each carrying the rule that drew it. */
    static List<Cut> cutsOf(Type type, Symbols symbols) {
        Bounds bounds = boundsOf(type, symbols);
        if (bounds == null || bounds.isEmpty() || !(type instanceof Type.Ref ref)) {
            return List.of();
        }
        Map<String, Cut> byValue = new LinkedHashMap<>();
        if (bounds.min != null) {
            put(byValue, numeric(bounds.min, bounds.decimal), ref.name(), "min");
        }
        if (bounds.max != null) {
            put(byValue, numeric(bounds.max, bounds.decimal), ref.name(), "max");
        }
        return List.copyOf(byValue.values());
    }

    private static void put(Map<String, Cut> into, ObservedValue value, TypeName type, String clause) {
        OriginRef origin = new OriginRef.InvariantOrigin(Optional.<SourceRef>empty(), type, clause);
        into.merge(String.valueOf(value), Cut.at(value, origin), (had, _) -> had.and(origin));
    }

    // --- small helpers ----------------------------------------------------------------------------

    /** Values that could stand for a type wherever nothing else has been said about the position — the
     * inner value of a newtype, a field no axis divides. A record is not one of these: its fields are
     * composed, which is the generator's work and not a value this can hand over. */
    static List<FixtureTemplate> representativesOf(Type type, Symbols symbols) {
        if (type == null) {
            return List.of();
        }
        if (type == Type.INT) {
            return List.of(FixtureTemplate.integer(0));
        }
        if (type == Type.DECIMAL) {
            return List.of(FixtureTemplate.decimal(BigDecimal.ZERO));
        }
        if (type == Type.STRING) {
            return List.of(FixtureTemplate.string("x"));
        }
        if (type == Type.BOOL) {
            return List.of(FixtureTemplate.bool(true));
        }
        // A date is built from its ISO 8601 form, which is how a row writes one. One fixed day rather
        // than today's: a generated row is compared with the last one to see what changed, and a value
        // that read the clock would change every time nothing had.
        if (type == Type.DATE) {
            return List.of(FixtureTemplate.date("2000-01-01"));
        }
        if (type == Type.DATETIME) {
            return List.of(FixtureTemplate.dateTime("2000-01-01T00:00:00"));
        }
        // The empty one, for every collection. It is the value that always builds — a rule about a
        // collection bounds its size or its elements, and neither can refuse having none — and a row
        // whose collection is not what it is about should say so by carrying nothing.
        if (type instanceof Type.ListOf || type instanceof Type.SetOf || type instanceof Type.MapOf) {
            return List.of(FixtureTemplate.emptyCollection());
        }
        List<PartitionClass> classes = classesOf(type, symbols);
        for (PartitionClass each : classes) {
            if (each.generatable()) {
                return each.representatives().candidates();
            }
        }
        // A newtype the model only bounds has no classes — everything outside the bound is refused at
        // construction — but it does have values, and the edge of the bound is one that builds.
        if (type instanceof Type.Ref ref && symbols.get(ref.name()) instanceof Ast.Data data
                && data.newtype()) {
            return insideTheNewtype(ref.name(), symbols).stream()
                    .map(t -> FixtureTemplate.newtype(ref.name(), t)).toList();
        }
        return List.of();
    }

    /**
     * What a newtype wraps: every value for it this can think of, in the order to try them.
     *
     * <p>Candidates, not an answer. Whether a newtype accepts a value is decided by its own
     * constructor, and this only proposes — so a rule it reads is a reason to offer another value
     * rather than to withdraw the ones already there. A format rule that cannot be read leaves the
     * position with what it had before this could read any of them, and a newtype carrying two rules
     * gets a value from each, which is why the order they are declared in does not decide whether one
     * builds.
     *
     * <p>Both the bound on a number and the format of a string, in one place, because a newtype is
     * asked for a value from two: a field of a record, and a case of a sum. Reading the rules in only
     * one of them is how a value that holds everywhere came to be written in one place and not the
     * other.
     */
    private static List<FixtureTemplate> insideTheNewtype(TypeName newtype, Symbols symbols) {
        Type base = TypeOps.newtypeInner(newtype, symbols);
        List<FixtureTemplate> candidates = new ArrayList<>();

        Bounds bounds = boundsOf(new Type.Ref(newtype), symbols);
        if (bounds != null && !bounds.isEmpty()) {
            candidates.add(bounds.decimal()
                    ? FixtureTemplate.decimal(inside(bounds))
                    : FixtureTemplate.integer(inside(bounds).longValueExact()));
        }
        if (base == Type.STRING && symbols.get(newtype) instanceof Ast.Data data) {
            for (Ast.InvariantClause clause : TypeOps.effectiveInvariants(data, symbols)) {
                for (Ast.Expr each : InvariantConstraints.clauses(clause.expr())) {
                    if (InvariantConstraints.of(each, base).orElse(null)
                            instanceof InvariantConstraints.Pattern format) {
                        PatternValues.shortestAccepted(format.regex())
                                .map(FixtureTemplate::string).ifPresent(candidates::add);
                    }
                }
            }
        }
        candidates.addAll(representativesOf(base, symbols));

        Map<String, FixtureTemplate> once = new LinkedHashMap<>();
        for (FixtureTemplate each : candidates) {
            once.putIfAbsent(each.text(), each);
        }
        return List.copyOf(once.values());
    }

    /** A number the bound admits. The lower edge where there is one: it is inside whatever upper edge
     * there is, and it is the value a boundary wants written anyway. */
    private static BigDecimal inside(Bounds bounds) {
        return bounds.min() != null ? bounds.min()
                : bounds.max() != null ? bounds.max() : BigDecimal.ZERO;
    }

    private static boolean isBool(ObservedValue v, boolean expected) {
        return v instanceof ObservedValue.Bool b && b.value() == expected;
    }

    private static ObservedValue numeric(BigDecimal value, boolean decimal) {
        return decimal ? new ObservedValue.Decimal(value)
                : new ObservedValue.Integer(value.longValueExact());
    }

    private static BigDecimal highest(BigDecimal had, BigDecimal one) {
        return had == null || one.compareTo(had) > 0 ? one : had;
    }

    private static BigDecimal lowest(BigDecimal had, BigDecimal one) {
        return had == null || one.compareTo(had) < 0 ? one : had;
    }

    private Partitions() {}
}
