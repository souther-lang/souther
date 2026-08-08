package souther.compiler.partition;

import souther.compiler.ast.Ast;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.check.FieldDomains;
import souther.compiler.check.InvariantBound;
import souther.compiler.codegen.InvariantConstraints;
import souther.compiler.diag.SourceRef;
import souther.compiler.observe.Incompleteness;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.NumericDomain;
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
    public record Partitioning(List<Axis> axes, List<OmittedAxis> omitted,
                               Map<String, NumericDomain.Bounds> domains,
                               java.util.Set<String> uncertain) {
        public Partitioning {
            axes = List.copyOf(axes);
            omitted = List.copyOf(omitted);
            domains = Map.copyOf(domains);
            uncertain = java.util.Set.copyOf(uncertain);
        }

        /** Whether an edge of this position is a value some row could carry.
         *
         * <p>False where a rule reaching the value this position sits in was not read in full. Every
         * edge here is then where the rules this could read stop, and a rule it could not read can
         * refuse that value as easily as the one beyond it — so the edge is not known to be writable
         * and asking for a row at it is asking for work nobody may be able to do. */
        public boolean edgeIsKnownWritable(String path) {
            return !uncertain.contains(path);
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
        Map<String, NumericDomain.Bounds> domains = new LinkedHashMap<>();
        java.util.Set<String> uncertain = new java.util.LinkedHashSet<>();
        for (int i = 0; i < sig.inputTypes().size() && i < behavior.params().size(); i++) {
            // One reading per parameter, not one per record met on the way down. A clause on the
            // outer record relates positions at any depth it can name, and rebuilding the reading at
            // each record is how `interval.startsAt < cap` stopped reaching `interval.startsAt`.
            Type type = sig.inputTypes().get(i);
            walk(behavior.name(), TermPath.of(behavior.params().get(i).name()), type,
                    0, symbols, found, new Placed(nameOf(type), fieldDomainsOf(type, symbols)),
                    domains, uncertain);
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
        return new Partitioning(kept, omitted, domains, uncertain);
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
            // What this position can hold, which is the type's bound already narrowed by whatever
            // the record it sits in says about it. Reading the type again here would put a threshold
            // back inside a range the record has no values in.
            NumericDomain.Bounds domain = base.domains().get(axis.path().toString());
            BigDecimal min = domain == null || domain.min() == null ? null : domain.min().value();
            BigDecimal max = domain == null || domain.max() == null ? null : domain.max().value();
            // Filtered once, and both answers read the filtered list. A line outside what the
            // position holds divides nothing, and it is not a boundary either: leaving it in the
            // cuts while the intervals dropped it asks for a row at a value the record refuses,
            // which is the thing being fixed here happening again one field over. The end the
            // position stops short of is outside it as much as anything past it is.
            List<Threshold> reachable = here.stream()
                    .filter(t -> domain == null || domain.admits(t.value()))
                    .toList();
            List<PartitionClass> classes = Intervals.classesOf(
                    Intervals.of(reachable, min, max), axis.path(), axis.type(), symbols);
            // What the position is, not what an invariant said about it. There is a bound to read
            // only where the type is a newtype carrying one, and a plain `Decimal` has none — read
            // off the bound, every such position would be called an integer and a threshold of
            // `0.5m` would be asked for its exact `long`.
            boolean decimal = TypeOps.base(axis.type(), symbols) == Type.DECIMAL;
            // Through `excluding`, so that a class list replaced by the intervals a threshold cuts
            // keeps only the exclusions it still has classes for.
            out.add(new Axis(axis.id(), axis.path(), axis.type(),
                    classes.isEmpty() ? axis.classes() : classes,
                    merged(axis.cuts(), reachable, decimal)).excluding(axis.excluded()));
        }
        return new Partitioning(out, base.omitted(), base.domains(), base.uncertain());
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
    public static List<BoundaryObligation> obligationsOf(Axis axis, Symbols symbols,
                                                         NumericDomain.Bounds within) {
        boolean decimal = TypeOps.base(axis.type(), symbols) == Type.DECIMAL;
        BoundaryDomain domain = decimal ? BoundaryDomain.DECIMAL : BoundaryDomain.INT;
        List<BoundaryObligation> out = new ArrayList<>();
        for (Cut cut : axis.cuts()) {
            // A line the position does not reach. The rule that drew it did so about the type, and
            // what is left of the type here may stop short of it or leave the value out — `low < high`
            // under one `[0, 1]` leaves `low` every value up to 1 and not 1 itself. Writing the value
            // is how an edge is met, so where the value is refused there is nothing to write.
            boolean reachable = holds(within, cut.value());
            for (OriginRef origin : cut.origins()) {
                if (reachable) {
                    out.add(new BoundaryObligation(axis.id(), origin,
                            BoundaryObligation.BoundarySide.AT, cut.value()));
                }
                if (origin instanceof OriginRef.GuardOrigin guard) {
                    // The other class's edge is the neighbour on the side the cut value is not on —
                    // where that class has values. A guard at the end of what the position can hold
                    // has nothing on one side of it, and a step off the end is a row nobody can write:
                    // `value >= 10` under `x < 10` would be owed a 9. The cut itself stays either way,
                    // because the comparison is still reached by a row written at the line.
                    if (guard.valueBelongsBelow()) {
                        domain.successor(cut.value()).filter(next -> holds(within, next))
                                .ifPresent(next -> out.add(new BoundaryObligation(
                                        axis.id(), origin,
                                        BoundaryObligation.BoundarySide.ABOVE, next)));
                    } else {
                        domain.predecessor(cut.value()).filter(before -> holds(within, before))
                                .ifPresent(before -> out.add(new BoundaryObligation(
                                        axis.id(), origin,
                                        BoundaryObligation.BoundarySide.BELOW, before)));
                    }
                }
            }
        }
        return List.copyOf(out);
    }

    /** Whether a value invented one step off a line is one the position can hold. */
    private static boolean holds(NumericDomain.Bounds within, ObservedValue value) {
        if (within == null) {
            return true;
        }
        BigDecimal number = switch (value) {
            case ObservedValue.Integer i -> BigDecimal.valueOf(i.value());
            case ObservedValue.Decimal d -> d.value();
            case null, default -> null;
        };
        if (number == null) {
            return true;
        }
        return within.admits(number);
    }

    /** One position: measured where the model divides it or bounds it, taken apart where it is a
     * record, and recorded as not derivable where it is neither. */
    private static void walk(String behavior, TermPath path, Type type, int depth, Symbols symbols,
                             List<Axis> out, Placed placed,
                             Map<String, NumericDomain.Bounds> domains,
                             java.util.Set<String> uncertain) {
        AxisId id = AxisId.of(behavior, path);
        List<PartitionClass> classes = classesOf(type, symbols);
        Bounds own = boundsOf(type, symbols);
        // A value whose rules contradict has no positions to cover: every edge of every field of it
        // is a row nobody can write, which is not the same answer as a field nothing bounds.
        boolean nothingExists = placed != null && placed.domains().infeasible();
        NumericDomain.Bounds projected = placed == null ? null : placed.at(path);
        // Two questions of one pair of readings, and they do not have one answer. What the position
        // can hold is every rule about it intersected; where it is divided is only where its own type
        // draws a line, because a clause relating two fields is not a partition of one of them.
        NumericDomain.Bounds admissible = nothingExists ? null : admissibleBounds(own, projected);
        if (admissible != null && !admissible.isEmpty()) {
            domains.put(path.toString(), admissible);
        }
        Bounds axis = nothingExists ? null : axisBounds(own, projected);
        List<Cut> cuts = nothingExists ? List.of()
                : cutsOf(type, axis, own, placed == null ? null : placed.value());
        // Whether a row can be written at an edge is a question about the whole value the position
        // sits in, so it is answered once for the parameter. A rule this could not read is a way that
        // value can be refused, wherever in it the rule is written.
        if (!cuts.isEmpty() && placed != null && !placed.domains().allRulesRead()) {
            uncertain.add(path.toString());
        }
        if (!classes.isEmpty() || !cuts.isEmpty()) {
            out.add(new Axis(id, path, type, classes, cuts));
            return;
        }
        Map<String, Type> fields = productFields(type, symbols);
        if (!fields.isEmpty() && depth < MAX_DEPTH) {
            for (Map.Entry<String, Type> field : fields.entrySet()) {
                walk(behavior, path.then(field.getKey()), field.getValue(), depth + 1, symbols, out,
                        placed, domains, uncertain);
            }
            return;
        }
        out.add(Axis.notDerivable(id, path, type));
    }

    /** The value a position is inside: what it is called, and what its rules leave each position of
     * it able to hold. */
    private record Placed(TypeName value, FieldDomains domains) {

        /** What is left for the position at {@code path}, which is read from the value this is of. */
        NumericDomain.Bounds at(TermPath path) {
            return path.fields().isEmpty() ? null
                    : domains.at(String.join(".", path.fields()));
        }
    }

    private static TypeName nameOf(Type type) {
        return type instanceof Type.Ref ref ? ref.name() : null;
    }

    /** What the record a field sits in leaves each of its fields able to hold. */
    private static FieldDomains fieldDomainsOf(Type type, Symbols symbols) {
        return type instanceof Type.Ref ref && symbols.get(ref.name()) instanceof Ast.Data data
                ? FieldDomains.of(ref.name(), data, symbols) : FieldDomains.NONE;
    }

    /**
     * Where the position is divided: the type's own bound, taken in to where the record it sits in
     * stops.
     *
     * <p>Only taken in. A record's rule moves an edge the type already has; it does not put one on a
     * position the type left open. An {@code Int} nobody bounded stays a position the model draws no
     * line through, which is what a report says of it (ADR-0090) — giving it an edge here would make
     * a rule relating two fields into a partition of one of them.
     *
     * <p>So this is not what the position can hold, and reading it as that is how a cap written on
     * the record alone became invisible: see {@link #admissibleBounds}.
     */
    private static Bounds axisBounds(Bounds own, NumericDomain.Bounds projected) {
        if (own == null || projected == null) {
            return own;
        }
        // The value moves and the names do not: a record narrowing an edge does not take it away
        // from the rule that put one there, and which record did the narrowing is said beside it.
        return new Bounds(
                own.min() == null ? null
                        : new End(Endpoint.lower(own.min().at(), projected.min()), own.min().from()),
                own.max() == null ? null
                        : new End(Endpoint.upper(own.max().at(), projected.max()), own.max().from()),
                own.decimal());
    }

    /**
     * What the position can hold: every rule reaching it, intersected.
     *
     * <p>An end survives from whichever side has one, because a value outside it is refused whether
     * the type said so or the record did. That is the difference from {@link #axisBounds}: a cap the
     * record alone imposes is not a line dividing this position, and it is still where its values
     * stop — so a guard beyond it divides nothing and is no edge either.
     *
     * <p>Numbers and no names. An end here says where the values stop; which rule put it there is a
     * cut's question, and answering it from a projection would name a rule that never mentioned this
     * position on its own.
     */
    private static NumericDomain.Bounds admissibleBounds(Bounds own, NumericDomain.Bounds projected) {
        if (own == null) {
            return null;   // not a number, so nothing bounds it either way
        }
        Endpoint min = own.min() == null ? null : own.min().at();
        Endpoint max = own.max() == null ? null : own.max().at();
        return projected == null ? new NumericDomain.Bounds(min, max)
                : new NumericDomain.Bounds(Endpoint.lower(min, projected.min()),
                        Endpoint.upper(max, projected.max()));
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
    /**
     * One end of a range, and every name that put it there.
     *
     * <p>Names, plural. Two layers can state the same bound — a wrapper repeating what it wraps — and
     * they are two rules a row could be owed to, which is the accounting a cut already keeps. Holding
     * one would drop an obligation rather than a line of text.
     */
    private record End(Endpoint at, List<TypeName> from) {

        BigDecimal value() {
            return at.value();
        }

        /**
         * This end, or {@code other} where it is the stronger, or both where they agree.
         *
         * <p>Which number survives and whether the value is one of the range's own are the same
         * question asked of {@link Endpoint}, so that this and the domain cannot disagree about it.
         * Where the two are at one number both names are kept: each is a rule the line is owed to,
         * however far into the range each of them reaches.
         */
        static End tighter(End had, End one, boolean upper) {
            if (one == null) {
                return had;
            }
            if (had == null) {
                return one;
            }
            Endpoint at = upper ? Endpoint.upper(had.at(), one.at()) : Endpoint.lower(had.at(), one.at());
            if (had.value().compareTo(one.value()) != 0) {
                return at == had.at() ? had : one;
            }
            List<TypeName> both = new ArrayList<>(had.from());
            one.from().stream().filter(n -> !both.contains(n)).forEach(both::add);
            return new End(at, List.copyOf(both));
        }
    }

    /**
     * What a newtype's rules leave the value between, and which of the names it wears said so.
     *
     * <p>The layer is kept because a boundary is reported by the rule that drew it, and a value
     * wearing two names is bounded by rules written on either. Read off the outermost name, an edge
     * that `Minute` drew would be reported as `StartMinute`'s.
     */
    private record Bounds(End min, End max, boolean decimal) {

        boolean isEmpty() {
            return min == null && max == null;
        }

    }

    private static Bounds boundsOf(Type type, Symbols symbols) {
        Type base = TypeOps.numericBase(type, symbols);
        if (base == null) {
            return null;
        }
        End min = null;
        End max = null;
        // Every name the value wears, not the outermost one. A rule written on the type a newtype
        // wraps bounds the value as much as one written on the newtype does, and the two intersect:
        // `Inner: value >= 0` under `Outer: value <= 10` is a range of `[0, 10]`, and neither layer
        // alone says so. How far that reaches is asked of `TypeOps` rather than walked again here,
        // and every layer that put an end where it is is kept, because each is a rule a row is owed.
        for (TypeOps.Layer layer : TypeOps.newtypeChain(type, symbols)) {
            for (Ast.InvariantClause clause : TypeOps.effectiveInvariants(layer.data(), symbols)) {
                for (Ast.Expr each : InvariantConstraints.clauses(clause.expr())) {
                    InvariantBound read = InvariantBound.of(each, base).orElse(null);
                    if (read == null) {
                        continue;
                    }
                    End end = new End(read.end(), List.of(layer.named()));
                    if (read.lower()) {
                        min = End.tighter(min, end, false);
                    } else {
                        max = End.tighter(max, end, true);
                    }
                }
            }
        }
        return new Bounds(min, max, base == Type.DECIMAL);
    }

    /** The cuts of a position, each carrying the rule that drew it. */
    /**
     * The cuts of a position whose range is already settled.
     *
     * @param bounds where the position stops, the record it sits in taken into account
     * @param own    where its own type stops, so that an end the record moved can say so
     * @param within the record, or null at a position that is not a field of one
     */
    private static List<Cut> cutsOf(Type type, Bounds bounds, Bounds own, TypeName within) {
        if (bounds == null || bounds.isEmpty() || !(type instanceof Type.Ref)) {
            return List.of();
        }
        Map<String, Cut> byValue = new LinkedHashMap<>();
        cut(byValue, bounds.min(), own == null ? null : own.min(), "min", bounds.decimal(), within);
        cut(byValue, bounds.max(), own == null ? null : own.max(), "max", bounds.decimal(), within);
        return List.copyOf(byValue.values());
    }

    /** One end as a cut, owed once to each rule that put it there. */
    private static void cut(Map<String, Cut> into, End end, End own, String clause, boolean decimal,
                            TypeName within) {
        if (end == null) {
            return;
        }
        boolean moved = own != null && own.value().compareTo(end.value()) != 0;
        for (TypeName from : end.from()) {
            put(into, numeric(end.value(), decimal), from, clause, moved ? within : null);
        }
    }

    /** Whether an end is somewhere other than where the type's own rule left it. */
    private static boolean moved(BigDecimal own, BigDecimal effective) {
        return own != null && own.compareTo(effective) != 0;
    }

    private static void put(Map<String, Cut> into, ObservedValue value, TypeName type, String clause,
                            TypeName narrowedBy) {
        OriginRef origin = new OriginRef.InvariantOrigin(Optional.<SourceRef>empty(), type, clause);
        if (narrowedBy != null) {
            origin = new OriginRef.NarrowedOrigin(origin, narrowedBy);
        }
        OriginRef each = origin;
        into.merge(String.valueOf(value), Cut.at(value, origin), (had, _) -> had.and(each));
    }

    // --- small helpers ----------------------------------------------------------------------------

    /** Values that could stand for a type wherever nothing else has been said about the position — the
     * inner value of a newtype, a field no axis divides. A record is not one of these: its fields are
     * composed, which is the generator's work and not a value this can hand over. */
    static List<FixtureTemplate> representativesOf(Type type, Symbols symbols) {
        return representativesOf(type, symbols, null);
    }

    /**
     * The same, for a position the record it sits in has already narrowed.
     *
     * <p>{@code within} is what is left of the position once the rest of the assignment is settled:
     * an {@code endsAt} beside a {@code startsAt} of 1439 can only be 1440, and the value this offers
     * has to come from there rather than from the bottom of the type's own range.
     */
    static List<FixtureTemplate> representativesOf(Type type, Symbols symbols,
                                                   NumericDomain.Bounds within) {
        if (type == null) {
            return List.of();
        }
        if (type == Type.INT || type == Type.DECIMAL) {
            BigDecimal value = inside(within, type == Type.DECIMAL);
            return value == null ? List.of()
                    : List.of(type == Type.INT ? FixtureTemplate.integer(value.longValueExact())
                            : FixtureTemplate.decimal(value));
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
            return insideTheNewtype(ref.name(), symbols, within).stream()
                    .map(t -> FixtureTemplate.newtype(ref.name(), t)).toList();
        }
        return List.of();
    }

    /**
     * The same, with a second value offered at a numeric position.
     *
     * <p>One value is enough only where the rules that decide it are the rules the projection holds.
     * A disequality is a hole no range keeps, and a form that is neither an interval nor a difference
     * is not recorded at all — so the value a range gives up can be one those rules refuse, and a
     * position offering only that has nothing left to try.
     *
     * <p>Displaced and not invented. A whole number has a next one; a decimal between two ends has a
     * midpoint, and where it has no second end it gets no second value, because an epsilon is a value
     * the type does not name. A candidate is a proposal the decoder answers — it carries no promise
     * that the value is writable, which is what separates this from a boundary a person is asked to
     * write.
     */
    static List<FixtureTemplate> displacedRepresentativesOf(Type type, Symbols symbols,
                                                            NumericDomain.Bounds within) {
        List<FixtureTemplate> base = new ArrayList<>(representativesOf(type, symbols, within));
        // What a position holds back for the product search's second pass is on offer here from the
        // start. This pass runs only where both of those have already failed, and a position keeping
        // a value from the last search there is a value nothing will ever be tried at.
        for (FixtureTemplate held : inReserve(type, symbols, within)) {
            if (base.stream().noneMatch(each -> each.text().equals(held.text()))) {
                base.add(held);
            }
        }
        Type numeric = TypeOps.numericBase(type, symbols);
        if (numeric == null) {
            return List.copyOf(base);
        }
        NumericDomain.Bounds range = admissibleBounds(boundsOf(type, symbols), within);
        BigDecimal step = displaced(range, numeric == Type.INT);
        if (step == null) {
            return List.copyOf(base);
        }
        FixtureTemplate bare = numeric == Type.DECIMAL ? FixtureTemplate.decimal(step)
                : FixtureTemplate.integer(step.longValueExact());
        FixtureTemplate value = type instanceof Type.Ref ref
                && symbols.get(ref.name()) instanceof Ast.Data data && data.newtype()
                ? FixtureTemplate.newtype(ref.name(), bare) : bare;
        if (base.stream().anyMatch(each -> each.text().equals(value.text()))) {
            return List.copyOf(base);
        }
        base.add(value);
        return List.copyOf(base);
    }

    /** A second number of a range, or null where the type has none to give. */
    private static BigDecimal displaced(NumericDomain.Bounds range, boolean whole) {
        BigDecimal from = inside(range, !whole);
        if (from == null) {
            return null;
        }
        Endpoint min = range == null ? null : range.min();
        Endpoint max = range == null ? null : range.max();
        if (!whole) {
            // No smallest step, so the only second value a range names is one inside both its ends —
            // and the one already on offer is that value where the range is open below.
            return min == null || max == null || !min.inclusive() ? null
                    : Endpoint.valueBetween(Endpoint.exclusive(min.value()), max, Granularity.DENSE);
        }
        BigDecimal up = from.add(BigDecimal.ONE);
        if (holdsNumber(range, up)) {
            return up;
        }
        BigDecimal down = from.subtract(BigDecimal.ONE);
        return holdsNumber(range, down) ? down : null;
    }

    /** Whether a range holds a number, with no range holding everything. */
    private static boolean holdsNumber(NumericDomain.Bounds range, BigDecimal value) {
        return range == null || range.admits(value);
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
        return insideTheNewtype(newtype, symbols, null);
    }

    private static List<FixtureTemplate> insideTheNewtype(TypeName newtype, Symbols symbols,
                                                          NumericDomain.Bounds within) {
        Type base = TypeOps.newtypeInner(newtype, symbols);
        List<FixtureTemplate> candidates = new ArrayList<>();

        Bounds own = boundsOf(new Type.Ref(newtype), symbols);
        NumericDomain.Bounds bounds = admissibleBounds(own, within);
        BigDecimal held = bounds == null || bounds.isEmpty() ? null : inside(bounds, own.decimal());
        if (held != null) {
            candidates.add(own.decimal() ? FixtureTemplate.decimal(held)
                    : FixtureTemplate.integer(held.longValueExact()));
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

    /** A number the position holds, or null where it holds none. The ends decide it, so nothing here
     * reads one of them as a number and loses whether the range reaches it. */
    private static BigDecimal inside(NumericDomain.Bounds within, boolean decimal) {
        Granularity spacing = decimal ? Granularity.DENSE : Granularity.DISCRETE;
        return within == null ? BigDecimal.ZERO
                : Endpoint.valueBetween(within.min(), within.max(), spacing);
    }

    /**
     * What a position can offer once everything it ordinarily offers has been refused.
     *
     * <p>The far edge of a range, for a position that is a bounded number. A rule relating this
     * position to another is what refuses the near one: `low < high` with `low` already fixed leaves
     * `high` a range starting at the value `low` took, and over decimals that range starts at the one
     * number the rule will not accept, because a strict bound there has no next value to step to. The
     * far edge is not knowing which number the rule wants — it is having a second number to be
     * refused at, which a range offering one edge does not.
     *
     * <p>Held back rather than offered beside the others, because what a row is searched for is the
     * product of what its positions offer and that search is bounded. A value added to one position
     * moves every assignment past it further back, so offering this one among the rest would lose
     * rows that were being reached at positions this has nothing to do with.
     */
    static List<FixtureTemplate> inReserve(Type type, Symbols symbols,
                                           NumericDomain.Bounds within) {
        if (!(type instanceof Type.Ref ref) || !(symbols.get(ref.name()) instanceof Ast.Data data)
                || !data.newtype()) {
            return List.of();
        }
        Bounds own = boundsOf(type, symbols);
        NumericDomain.Bounds bounds = admissibleBounds(own, within);
        // The far end has to be a value the position holds. Where the range stops short of it there
        // is nothing there to hold back, and a dense order has no value beside it to hold back
        // instead — what is inside is already what the first tier offers.
        if (bounds == null || bounds.min() == null || bounds.max() == null
                || !bounds.max().inclusive()
                || bounds.max().value().compareTo(bounds.min().value()) == 0) {
            return List.of();
        }
        BigDecimal far = bounds.max().value();
        FixtureTemplate held = FixtureTemplate.newtype(ref.name(), own.decimal()
                ? FixtureTemplate.decimal(far) : FixtureTemplate.integer(far.longValueExact()));
        // Nothing already on offer: a range whose far edge is the number the base type stands for
        // would otherwise hold the same value twice, once in each tier.
        return representativesOf(type, symbols, within).stream()
                .map(FixtureTemplate::text).anyMatch(held.text()::equals)
                ? List.of() : List.of(held);
    }

    private static boolean isBool(ObservedValue v, boolean expected) {
        return v instanceof ObservedValue.Bool b && b.value() == expected;
    }

    private static ObservedValue numeric(BigDecimal value, boolean decimal) {
        return decimal ? new ObservedValue.Decimal(value)
                : new ObservedValue.Integer(value.longValueExact());
    }

    private Partitions() {}
}
