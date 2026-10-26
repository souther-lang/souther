package souther.compiler.partition;

import souther.compiler.ast.Hir;
import souther.compiler.check.Carrier;
import souther.compiler.check.FieldDomains;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.PositionsAStatementReads;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.Place;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.TreeMap;
import java.util.function.Function;
import java.util.stream.IntStream;
import java.util.stream.Stream;

/**
 * Rows built for the two ways round the order of a repeated key, from a row that already stands at
 * the rule.
 *
 * <p>A composer writes the elements of a container alike, so it cannot write a key held by
 * elements that differ elsewhere. The row it did write is read back as the values its run
 * observed, and the container is written again with what it held kept: two of its elements are
 * given one key and one field set to different values, or one element is repeated and the two
 * copies are given different values. The fields and the values come from the declared types, and
 * the walk to the container is {@link BehaviorInputs}', so a name a position wears and a field
 * below a record are met the way a read of the same row meets them. What is written back goes
 * through {@link ObservedFixtures}, so a candidate is spelled the way any other value of the
 * position is.
 *
 * <p>These are candidates and no evidence. Whether the order decides the statement, and whether
 * the row still stands at the rule, are for a run to say ({@link CasesTheRowsTook#casesSeenBy}).
 * What a case can be looked for by is the same question as what is written for it
 * ({@link #of}), asked of the same plan.
 */
public final class KeyOrderCandidates {

    /** The most distinct values of one kind that two copies of an element are given between
     *  them. */
    static final int MOST_VALUES_OF_A_KIND = 6;

    /** The most rewrites of one row that are looked at, whether or not the decoder admits them. */
    static final int MOST_REWRITES_LOOKED_AT = 192;

    /** The most rewrites of one row that the decoder admits and that are handed on to be run. */
    static final int MOST_CANDIDATES = 48;

    /** How many records down an element a field is looked for to be given another value. */
    static final int MOST_LEVELS_OF_FIELDS = 3;

    private final BehaviorInputs inputs;

    private final Plan plan;

    /** What each type is under the declarations, worked out once for the rows of one search. */
    private final Function<Type, TypeView> views;

    private KeyOrderCandidates(BehaviorInputs inputs, Plan plan, Function<Type, TypeView> views) {
        this.inputs = inputs;
        this.plan = plan;
        this.views = views;
    }

    /** A field below an element, and what it is declared as. */
    private record Target(List<String> fields, Type type) {}

    /**
     * Where a key is held twice, and what is given another value to tell the two apart.
     *
     * @param parameter the parameter the container is a part of
     * @param container the list whose order decides the statement
     * @param key       the fields from an element to the key
     * @param element   what the container holds
     * @param targets   the fields below an element that can be given another value, nearest the
     *                  statement first
     */
    private record Plan(int parameter, TermPath container, List<String> key, Type element,
                        List<Target> targets, Map<List<String>, List<Place>> named) {}

    /**
     * Whether a row can be written for {@code target}: the container is a list reached through
     * fields and elements, the key is a field below its elements, and some other field below them
     * can be given another value.
     */
    public static boolean canRewrite(CaseOfAStatement.KeyOrder target, BehaviorInputs inputs) {
        return of(target, inputs).isPresent();
    }

    /**
     * What writes rows for {@code target}, planned once for all the rows a search rewrites; none
     * where {@link #canRewrite} is false.
     */
    public static Optional<KeyOrderCandidates> of(CaseOfAStatement.KeyOrder target,
                                                  BehaviorInputs inputs) {
        Function<Type, TypeView> views = inputs.cachedViews();
        Plan plan = planOf(target, inputs, views);
        return plan == null ? Optional.empty()
                : Optional.of(new KeyOrderCandidates(inputs, plan, views));
    }

    /**
     * The rows that write {@code base}, whose run observed {@code seen}, with the container
     * holding a key twice, as many as are asked for and no more are made.
     *
     * @param base the row the candidates are rewrites of
     * @param seen the values its run observed, one per parameter
     * @param writing what the row's parameters are and how a value of each is written, and what
     *                the decoder says of a value written at one: a rewrite it refuses is no row, as
     *                a value a search composed is none, and is never run
     */
    public Stream<RowToRun> refining(RowToRun base, List<ObservedValue> seen,
                                     RowWriting writing) {
        if (plan.parameter() >= seen.size() || plan.parameter() >= base.inputs().size()) {
            return Stream.empty();
        }
        MeasuredInput subject = writing.subject();
        Pool pool = Pool.of(seen, prim -> composedAt(subject, prim), subject.ruleReading());
        List<List<String>> apart = subject.keptApartAt(plan.container());
        // Two bounds, because the decoder refuses some of what is looked at: counting only what
        // it admits would let a rule that refuses nearly everything be looked at without end, and
        // counting what is looked at would let the refused ones use up the rows that are run.
        return inputs.rewritingBelow(seen.get(plan.parameter()),
                        inputs.types().get(plan.parameter()), plan.container().steps(),
                        (here, _, _) -> heldTwice(here, pool, apart), views)
                .limit(MOST_REWRITES_LOOKED_AT)
                .map(each -> ObservedFixtures.of(each, subject.types().get(plan.parameter()),
                        subject.ruleReading()))
                .filter(ObservedFixtures.Writing.Written.class::isInstance)
                .map(written -> ((ObservedFixtures.Writing.Written<FixtureTemplate>) written)
                        .value())
                .filter(value -> writing.check().refuse(plan.parameter(), value).isEmpty())
                .limit(MOST_CANDIDATES)
                .map(value -> {
                    List<FixtureTemplate> values = new ArrayList<>(base.inputs());
                    values.set(plan.parameter(), value);
                    return new RowToRun(values, base.answers());
                });
    }

    private static Plan planOf(CaseOfAStatement.KeyOrder target, BehaviorInputs inputs,
                               Function<Type, TypeView> views) {
        TermPath container = target.order().container();
        List<String> key = fieldsBelowAnElement(container, target.order().position());
        int parameter = inputs.parameters().indexOf(container.head());
        if (key == null || parameter < 0 || !container.steps().stream().allMatch(each ->
                each instanceof TermPath.Step.Field || each instanceof TermPath.Step.Element)) {
            return null;
        }
        Type held = inputs.typeRead(inputs.types().get(parameter), container.steps(), views);
        // A set has no order to repeat a key in.
        if (held == null || !(views.apply(held).shape() instanceof Shape.Sequence list)
                || list.kind() != Shape.Sequence.Kind.LIST
                || inputs.typeRead(list.element(), fieldSteps(key), views) == null) {
            return null;
        }
        List<Target> targets = targetsOf(inputs, views, list.element(), key,
                readBy(target.statement(), container));
        return targets.isEmpty() ? null
                : new Plan(parameter, container, key, list.element(), targets,
                        namedBy(target.statement(), container));
    }

    /** The fields from an element of {@code container} to {@code position}, or null where it is
     *  not a field path below one. */
    private static List<String> fieldsBelowAnElement(TermPath container, TermPath position) {
        List<TermPath.Step> within = container.steps();
        List<TermPath.Step> steps = position.steps();
        if (!position.head().equals(container.head()) || steps.size() <= within.size() + 1
                || !steps.subList(0, within.size()).equals(within)
                || !(steps.get(within.size()) instanceof TermPath.Step.Element)) {
            return null;
        }
        List<String> fields = new ArrayList<>();
        for (TermPath.Step each : steps.subList(within.size() + 1, steps.size())) {
            if (!(each instanceof TermPath.Step.Field(String name))) {
                return null;
            }
            fields.add(name);
        }
        return fields;
    }

    /** The fields below an element that {@code stated} reads, in the order it names them, or null
     *  where it is not known which: a field it does not read cannot change what it comes to. */
    private static List<List<String>> readBy(Proposition stated, TermPath container) {
        Optional<List<TermPath>> places = PositionsAStatementReads.everyPlaceOf(stated);
        if (places.isEmpty()) {
            return null;
        }
        List<List<String>> out = new ArrayList<>();
        for (TermPath place : places.get()) {
            List<String> below = fieldsBelowAnElement(container, place);
            if (below != null && !out.contains(below)) {
                out.add(below);
            }
        }
        return out.isEmpty() ? null : out;
    }

    private static List<TermPath.Step> fieldSteps(List<String> names) {
        return names.stream().<TermPath.Step>map(TermPath.Step.Field::new).toList();
    }

    /** The fields that can be given another value, other than the key and what holds or is held
     *  by it: the ones the statement reads where that is known, and otherwise every one. */
    private static List<Target> targetsOf(BehaviorInputs inputs, Function<Type, TypeView> views,
                                          Type element, List<String> key,
                                          List<List<String>> reads) {
        List<List<String>> fields = reads != null ? reads
                : leavesBelow(views, element, List.of(), 0);
        List<Target> out = new ArrayList<>();
        for (List<String> each : fields) {
            Type type = inputs.typeRead(element, fieldSteps(each), views);
            if (type != null && !startsWith(each, key) && !startsWith(key, each)
                    && variesAsAValue(views.apply(type).shape())) {
                out.add(new Target(each, type));
            }
        }
        return out;
    }

    private static boolean startsWith(List<String> names, List<String> prefix) {
        return names.size() >= prefix.size() && names.subList(0, prefix.size()).equals(prefix);
    }

    /** Every field below {@code type} that is a value to be given another, in the order the
     *  declarations write them. */
    private static List<List<String>> leavesBelow(Function<Type, TypeView> views, Type type,
                                                  List<String> reached, int levels) {
        Shape shape = views.apply(type).shape();
        if (!reached.isEmpty() && variesAsAValue(shape)) {
            return List.of(reached);
        }
        if (!(shape instanceof Shape.Product product) || levels >= MOST_LEVELS_OF_FIELDS) {
            return List.of();
        }
        List<List<String>> out = new ArrayList<>();
        product.fields().forEach((name, held) -> {
            List<String> next = new ArrayList<>(reached);
            next.add(name);
            out.addAll(leavesBelow(views, held, next, levels + 1));
        });
        return out;
    }

    /**
     * Whether a field of this shape can be given another value. Asked of the shape and nothing
     * else: a sum has another value wherever it has another case, and what is written for each
     * case is {@link #valuesFor}'s to find.
     */
    private static boolean variesAsAValue(Shape shape) {
        return switch (shape) {
            case Shape.Scalar scalar -> scalar.prim() != Type.Prim.RATIONAL;
            case Shape.Sum sum -> sum.reaches().cases().size() >= 2;
            default -> false;
        };
    }

    /**
     * The values a field of {@code type}, standing at {@code fields} below an element, is given.
     * A number, a text or a date is given the ones the statement compares the field with, the ones
     * the row holds and the ones a row is composed with at the type, in that order: what the
     * statement names is where its answer turns. A sum is given one value of each of its cases,
     * written as a row writes a record, so that a case carrying something is another value of the
     * field like one that carries nothing.
     *
     * @param named what the statement compares this field with ({@link #namedBy})
     */
    private List<ObservedValue> valuesFor(Type type, List<String> fields, Pool pool,
                                          List<Place> named) {
        Shape shape = views.apply(type).shape();
        if (shape instanceof Shape.Sum) {
            return casesOf(type, fields, pool);
        }
        if (!(shape instanceof Shape.Scalar scalar)) {
            return List.of();
        }
        return scalarValues(scalar, pool, named);
    }

    private static List<ObservedValue> scalarValues(Shape.Scalar scalar, Pool pool,
                                                    List<Place> named) {
        List<ObservedValue> held = switch (scalar.prim()) {
            case BOOL -> List.of(new ObservedValue.Bool(false), new ObservedValue.Bool(true));
            case INT -> pool.of(ObservedValue.Integer.class, scalar.prim());
            case DECIMAL -> pool.of(ObservedValue.Decimal.class, scalar.prim());
            case STRING -> pool.of(ObservedValue.Text.class, scalar.prim());
            case DATE, TIME, DATETIME, INSTANT ->
                    pool.of(ObservedValue.Temporal.class, scalar.prim());
            case RATIONAL -> List.of();
        };
        return scalar.prim() == Type.Prim.BOOL ? held
                : Stream.concat(namedAs(scalar.prim(), named).stream(), held.stream()).distinct()
                        .limit(MOST_VALUES_OF_A_KIND).toList();
    }

    /**
     * One value of each case of the sum {@code type}, in the order the declarations write the
     * cases. The case is the unit and not the value: a case with many values is given one, so that
     * the first case does not use up the room the others are listed in. A case nothing here writes
     * a value of is left out, which is a case this did not find and not one that cannot be.
     */
    private List<ObservedValue> casesOf(Type type, List<String> fields, Pool pool) {
        TypeView view = views.apply(type);
        if (!(view.shape() instanceof Shape.Sum sum)) {
            return List.of();
        }
        TermPath at = plan.container().element();
        for (String each : fields) {
            at = at.then(each);
        }
        List<ObservedValue> out = new ArrayList<>();
        for (TypeSymbol leaf : sum.reaches().cases()) {
            ValuesOfAnElement.Listed listed = ValuesOfAnElement.of(Type.ref(leaf), at,
                    pool.reading(), 1, (_, held) -> held.shape() instanceof Shape.Scalar scalar
                            ? scalarValues(scalar, pool, List.of()) : null);
            if (listed != null && !listed.values().isEmpty()) {
                out.add(ObservedValue.wrapped(view.wrappers(), listed.values().getFirst()));
            }
        }
        return out.stream().limit(MOST_VALUES_OF_A_KIND).toList();
    }

    /**
     * The values {@code stated} compares each field below an element of {@code container} with,
     * by the fields: a text or a number a field is set against. A whole number is named together
     * with the ones beside it, which are the two sides of where the comparison turns.
     *
     * <p>Only a comparison of a field with a written value is read; a comparison of a form of
     * several quantities names none, and the row's own values and the composer's stand for it.
     */
    private static Map<List<String>, List<Place>> namedBy(Proposition stated,
                                                          TermPath container) {
        Map<List<String>, List<Place>> out = new TreeMap<>(
                Comparator.comparing(Object::toString));
        collectNamed(stated, container, out);
        return out;
    }

    private static void collectNamed(Proposition stated, TermPath container,
                                     Map<List<String>, List<Place>> out) {
        if (stated instanceof Proposition.Compared(
                Relation.Ordered(DecisionAtom.OfTheInput(NumericTerm.ValueOf field), Place at, var _),
                var _, var _)) {
            List<String> below = fieldsBelowAnElement(container, field.position());
            if (below != null) {
                List<Place> places = out.computeIfAbsent(below, _ -> new ArrayList<>());
                if (!places.contains(at)) {
                    places.add(at);
                }
            }
        }
        stated.partsHeld().forEach(part -> collectNamed(part, container, out));
    }

    /**
     * The places a statement names at a field, as the values of a field declared as {@code prim}:
     * the carrier of the type says which places are its and what value each is, and a whole number
     * comes with the ones beside it. A place the carrier does not hold is not a value of the field.
     */
    private static List<ObservedValue> namedAs(Type.Prim prim, List<Place> places) {
        Carrier carrier = Carrier.ofPrimitive(prim);
        List<ObservedValue> out = new ArrayList<>();
        for (Place each : places) {
            if (carrier == null || carrier.onTheGrid(each) == null) {
                continue;
            }
            ObservedValue value = carrier.valueOf(each);
            out.add(value);
            if (value instanceof ObservedValue.Integer(long whole)) {
                if (whole > Long.MIN_VALUE) {
                    out.add(new ObservedValue.Integer(whole - 1));
                }
                if (whole < Long.MAX_VALUE) {
                    out.add(new ObservedValue.Integer(whole + 1));
                }
            }
        }
        return out;
    }

    /** What a composer would write at a scalar type, as the values an observation holds: the
     *  literals of the values it offers, and none that is not a literal. */
    private static List<ObservedValue> composedAt(MeasuredInput subject, Type.Prim prim) {
        List<ObservedValue> out = new ArrayList<>();
        for (FixtureTemplate each : subject.representativesHolding(prim,
                FieldDomains.ConstructionLimits.NONE).values()) {
            ObservedValue value = literalOf(each.value());
            if (value != null && !out.contains(value)) {
                out.add(value);
            }
        }
        return out;
    }

    private static ObservedValue literalOf(Hir.Expr written) {
        return switch (written) {
            case Hir.IntLit lit -> new ObservedValue.Integer(lit.value());
            case Hir.StringLit lit -> new ObservedValue.Text(lit.value());
            case Hir.DecimalLit lit -> new ObservedValue.Decimal(lit.value());
            case Hir.Neg(Hir.IntLit lit, var _, var _) ->
                    new ObservedValue.Integer(-lit.value());
            case Hir.Neg(Hir.DecimalLit lit, var _, var _) ->
                    new ObservedValue.Decimal(lit.value().negate());
            default -> null;
        };
    }

    /** What the container comes to with a key held twice, one rewrite at a time. */
    private Stream<ObservedValue> heldTwice(ObservedValue here, Pool pool,
                                            List<List<String>> apart) {
        if (!(here instanceof ObservedValue.Sequence(List<ObservedValue> elements))
                || elements.isEmpty()) {
            return Stream.empty();
        }
        return plan.targets().stream().flatMap(target -> {
            List<ObservedValue> values = valuesFor(target.type(), target.fields(), pool,
                    plan.named().getOrDefault(target.fields(), List.of()));
            return values.stream().flatMap(earlier -> values.stream()
                    .filter(later -> !later.equals(earlier))
                    .flatMap(later -> Stream.concat(
                            overwritten(elements, target, earlier, later),
                            repeated(elements, target, earlier, later, apart, pool))));
        });
    }

    /**
     * Two of the elements, the later given the key of the earlier and the two given the values
     * between them. Everything else each held stays, so a field that must differ between
     * elements, and the number of elements, are as they were.
     */
    private Stream<ObservedValue> overwritten(List<ObservedValue> elements, Target target,
                                              ObservedValue earlier, ObservedValue later) {
        return IntStream.range(0, elements.size()).boxed().flatMap(first ->
                IntStream.range(first + 1, elements.size()).boxed().map(second -> {
                    ObservedValue key = inputs.readingAt(elements.get(first), plan.element(),
                            plan.key(), views);
                    ObservedValue keyed = key == null ? null
                            : with(elements.get(second), plan.key(), key);
                    ObservedValue one = with(elements.get(first), target.fields(), earlier);
                    ObservedValue other = keyed == null ? null
                            : with(keyed, target.fields(), later);
                    if (one == null || other == null) {
                        return null;
                    }
                    List<ObservedValue> held = new ArrayList<>(elements);
                    held.set(first, one);
                    held.set(second, other);
                    return (ObservedValue) new ObservedValue.Sequence(held);
                })).filter(Objects::nonNull);
    }

    /**
     * One element repeated, the two copies given the values between them, beside everything else
     * the container held.
     *
     * <p>What the rules keep apart is a condition on the container that comes out, and is asked of
     * it: the copy is given another value at a field kept apart only where the container has it
     * equal to another element's there, and then one that no element of the container holds. A
     * field the two copies already differ at, because the order is told by it, is left as it is.
     */
    private Stream<ObservedValue> repeated(List<ObservedValue> elements, Target target,
                                           ObservedValue earlier, ObservedValue later,
                                           List<List<String>> apart, Pool pool) {
        return IntStream.range(0, elements.size()).boxed().map(at -> {
            ObservedValue one = with(elements.get(at), target.fields(), earlier);
            ObservedValue other = with(elements.get(at), target.fields(), later);
            if (one == null || other == null) {
                return null;
            }
            List<ObservedValue> held = new ArrayList<>(elements);
            held.set(at, one);
            held.add(at + 1, other);
            for (List<String> run : apart) {
                if (other != null && !startsWith(run, plan.key()) && !startsWith(plan.key(), run)) {
                    other = keptApartAt(held, at + 1, run, pool);
                    held.set(at + 1, other);
                }
            }
            return other == null ? null : (ObservedValue) new ObservedValue.Sequence(held);
        }).filter(Objects::nonNull);
    }

    /**
     * The element {@code at} of {@code held}, with a value at the fields {@code run} that no
     * other element holds there: itself where it already is so, and null where the field has no
     * such value to give. Taken from the ones its declared type is given ({@link #valuesFor}); not
     * made up for a type that neither the row, the statement nor the composer offers one of.
     */
    private ObservedValue keptApartAt(List<ObservedValue> held, int at, List<String> run,
                                      Pool pool) {
        ObservedValue element = held.get(at);
        ObservedValue mine = inputs.readingAt(element, plan.element(), run, views);
        Type type = inputs.typeRead(plan.element(), fieldSteps(run), views);
        if (mine == null || type == null) {
            return null;
        }
        Set<ObservedValue> elsewhere = new LinkedHashSet<>();
        for (int each = 0; each < held.size(); each++) {
            ObservedValue theirs = each == at ? null
                    : inputs.readingAt(held.get(each), plan.element(), run, views);
            if (theirs != null) {
                elsewhere.add(theirs);
            }
        }
        if (!elsewhere.contains(mine)) {
            return element;
        }
        ObservedValue another = valuesFor(type, run, pool,
                plan.named().getOrDefault(run, List.of())).stream()
                .filter(each -> !elsewhere.contains(each)).findFirst().orElse(null);
        return another == null ? null : with(element, run, another);
    }

    /** {@code element} with {@code replacement} at the fields {@code names} below it, or null
     *  where there is no such place in it. */
    private ObservedValue with(ObservedValue element, List<String> names,
                               ObservedValue replacement) {
        return inputs.rewritingBelow(element, plan.element(), fieldSteps(names),
                (_, _, _) -> Stream.of(replacement), views).findFirst().orElse(null);
    }

    /**
     * The values a row holds, by kind, in the order of a walk that does not depend on hashing,
     * and the ones a composer writes at the type: a field the row holds one value of is still
     * given another.
     */
    private static final class Pool {

        private final Map<Class<?>, Set<ObservedValue>> byKind = new HashMap<>();

        private final Function<Type.Prim, List<ObservedValue>> composed;

        /** The rules the values written are read under. */
        private final RuleReadingContext reading;

        private Pool(Function<Type.Prim, List<ObservedValue>> composed,
                     RuleReadingContext reading) {
            this.composed = composed;
            this.reading = reading;
        }

        static Pool of(List<ObservedValue> seen, Function<Type.Prim, List<ObservedValue>> composed,
                       RuleReadingContext reading) {
            Pool pool = new Pool(composed, reading);
            seen.forEach(pool::gather);
            return pool;
        }

        RuleReadingContext reading() {
            return reading;
        }

        List<ObservedValue> of(Class<?> kind, Type.Prim prim) {
            return Stream.concat(byKind.getOrDefault(kind, Set.of()).stream(),
                            composed.apply(prim).stream())
                    .distinct().limit(MOST_VALUES_OF_A_KIND).toList();
        }

        /** A whole number brings its neighbours, which are the values a comparison against it is
         *  cut by. */
        private void gather(ObservedValue value) {
            switch (value) {
                case ObservedValue.Integer(long n) -> {
                    Set<ObservedValue> ints = held(ObservedValue.Integer.class);
                    ints.add(value);
                    if (n > Long.MIN_VALUE) {
                        ints.add(new ObservedValue.Integer(n - 1));
                    }
                    if (n < Long.MAX_VALUE) {
                        ints.add(new ObservedValue.Integer(n + 1));
                    }
                }
                case ObservedValue.Decimal _, ObservedValue.Text _, ObservedValue.Temporal _ ->
                        held(value.getClass()).add(value);
                // In the order of the names: a record's fields are held unordered, and the values
                // two copies are given must not depend on which way a run hashed them.
                case ObservedValue.Constructed made -> new TreeMap<>(made.fields()).values()
                        .forEach(this::gather);
                case ObservedValue.Sequence sequence -> sequence.elements().forEach(this::gather);
                case ObservedValue.Mapping mapping -> mapping.entries().forEach(entry -> {
                    gather(entry.key());
                    gather(entry.value());
                });
                case ObservedValue.Bool _, ObservedValue.Unit _, ObservedValue.Absent _,
                     ObservedValue.Unknown _, ObservedValue.Truncated _ -> { }
            }
        }

        private Set<ObservedValue> held(Class<?> kind) {
            return byKind.computeIfAbsent(kind, _ -> new LinkedHashSet<>());
        }
    }
}
