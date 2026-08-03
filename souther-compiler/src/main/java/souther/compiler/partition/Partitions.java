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
     * @param axes    the positions this behavior is measured at, in parameter order
     * @param omitted axes past {@link #MAX_AXES}, dropped rather than merged: an axis whose path
     *                nobody can name is not an axis, and folding several into one would put a class
     *                nothing can classify into the denominator
     */
    public record Partitioning(List<Axis> axes, List<Incompleteness> omitted) {
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
    public static Partitioning of(Ast.SpecBehavior behavior, Sig sig, Symbols symbols) {
        List<Axis> found = new ArrayList<>();
        for (int i = 0; i < sig.ins().size() && i < behavior.params().size(); i++) {
            walk(behavior.name(), TermPath.of(behavior.params().get(i).name()), sig.ins().get(i),
                    0, symbols, found);
        }
        List<Axis> kept = new ArrayList<>();
        List<Incompleteness> omitted = new ArrayList<>();
        int measured = 0;
        for (Axis axis : found) {
            if (!axis.measurable()) {
                kept.add(axis);   // kept so a report can name what it could not measure
            } else if (measured < MAX_AXES) {
                kept.add(axis);
                measured++;
            } else {
                omitted.add(Incompleteness.of(Incompleteness.Code.AXIS_OMITTED, axis.id().toString()));
            }
        }
        return new Partitioning(kept, omitted);
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
                            RepresentativeSource.of("true")),
                    PartitionClass.of("false", "false", v -> isBool(v, false),
                            RepresentativeSource.of("false")));
        }
        if (type instanceof Type.OptionOf option) {
            List<FixtureTemplate> some = representativesOf(option.element(), symbols);
            return List.of(
                    PartitionClass.of("None", "None",
                            v -> v instanceof ObservedValue.Absent, RepresentativeSource.of("None")),
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
                    RepresentativeSource.of(leaf.name()));   // a unit case is its own name
        }
        if (data.newtype()) {
            List<FixtureTemplate> inner = representativesOf(TypeOps.newtypeInner(leaf, symbols),
                    symbols);
            return inner.isEmpty()
                    ? PartitionClass.ungeneratable(leaf.name(), leaf.name(), is,
                            "no value of what `" + leaf.name() + "` wraps can be written")
                    : PartitionClass.of(leaf.name(), leaf.name(), is,
                            () -> inner.stream()
                                    .map(t -> new FixtureTemplate(leaf.name() + "(" + t.text() + ")"))
                                    .toList());
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

    private static List<FixtureTemplate> representativesOf(Type type, Symbols symbols) {
        if (type == null) {
            return List.of();
        }
        if (type == Type.INT) {
            return List.of(new FixtureTemplate("0"));
        }
        if (type == Type.DECIMAL) {
            return List.of(new FixtureTemplate("0m"));
        }
        if (type == Type.STRING) {
            return List.of(new FixtureTemplate("\"x\""));
        }
        if (type == Type.BOOL) {
            return List.of(new FixtureTemplate("true"));
        }
        List<PartitionClass> classes = classesOf(type, symbols);
        for (PartitionClass each : classes) {
            if (each.generatable()) {
                return each.representatives().candidates();
            }
        }
        return List.of();
    }

    private static boolean isBool(ObservedValue v, boolean expected) {
        return v instanceof ObservedValue.Bool b && b.value() == expected;
    }

    private static int compare(ObservedValue v, BigDecimal against) {
        return switch (v) {
            case ObservedValue.Integer i -> BigDecimal.valueOf(i.value()).compareTo(against);
            case ObservedValue.Decimal d -> d.value().compareTo(against);
            case ObservedValue.Constructed c when c.field("value") != null ->
                    compare(c.field("value"), against);
            case null, default -> Integer.MIN_VALUE;
        };
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

    private static String plain(BigDecimal value) {
        return value.stripTrailingZeros().toPlainString();
    }

    private Partitions() {}
}
