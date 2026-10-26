package souther.compiler.partition;

import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.PositionsAStatementReads;
import souther.compiler.meaning.Proposition;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

import java.util.ArrayList;
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
                        List<Target> targets) {}

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
        Pool pool = Pool.of(seen);
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
                : new Plan(parameter, container, key, list.element(), targets);
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

    private static boolean variesAsAValue(Shape shape) {
        return shape instanceof Shape.Sum
                || (shape instanceof Shape.Scalar scalar && scalar.prim() != Type.Prim.RATIONAL);
    }

    /** The values a field of this shape is given: both of a {@code Bool}, the unit cases of a sum
     *  the declarations name, and of the rest the ones a row holds. */
    private List<ObservedValue> valuesFor(Shape shape, Pool pool) {
        return switch (shape) {
            case Shape.Scalar scalar -> switch (scalar.prim()) {
                case BOOL -> List.of(new ObservedValue.Bool(false), new ObservedValue.Bool(true));
                case INT -> pool.of(ObservedValue.Integer.class);
                case DECIMAL -> pool.of(ObservedValue.Decimal.class);
                case STRING -> pool.of(ObservedValue.Text.class);
                case DATE, TIME, DATETIME, INSTANT -> pool.of(ObservedValue.Temporal.class);
                case RATIONAL -> List.of();
            };
            case Shape.Sum sum -> sum.reaches().cases().stream()
                    .filter(each -> views.apply(Type.ref(each)).shape() instanceof Shape.Unit)
                    .<ObservedValue>map(ObservedValue.Unit::new)
                    .limit(MOST_VALUES_OF_A_KIND).toList();
            default -> List.of();
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
            List<ObservedValue> values = valuesFor(views.apply(target.type()).shape(), pool);
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
     * the container held. The copy is given another value at each field the rules keep the
     * elements apart at, other than the key: a repeated key is what is asked for, and a second
     * element equal to the first at what is kept apart is a container the rules refuse.
     */
    private Stream<ObservedValue> repeated(List<ObservedValue> elements, Target target,
                                           ObservedValue earlier, ObservedValue later,
                                           List<List<String>> apart, Pool pool) {
        return IntStream.range(0, elements.size()).boxed().map(at -> {
            ObservedValue one = with(elements.get(at), target.fields(), earlier);
            ObservedValue other = with(elements.get(at), target.fields(), later);
            for (List<String> run : apart) {
                if (other != null && !startsWith(run, plan.key()) && !startsWith(plan.key(), run)) {
                    ObservedValue held = inputs.readingAt(other, plan.element(), run, views);
                    ObservedValue another = held == null ? null : anotherThan(held, run, pool);
                    other = another == null ? null : with(other, run, another);
                }
            }
            if (one == null || other == null) {
                return null;
            }
            List<ObservedValue> held = new ArrayList<>(elements);
            held.set(at, one);
            held.add(at + 1, other);
            return (ObservedValue) new ObservedValue.Sequence(held);
        }).filter(Objects::nonNull);
    }

    /**
     * A value of the field at {@code names} that is not {@code value}, taken from the ones its
     * declared type is given ({@link #valuesFor}), or null where there is none: nothing is made up
     * for a type the row holds only one value of.
     */
    private ObservedValue anotherThan(ObservedValue value, List<String> names, Pool pool) {
        Type type = inputs.typeRead(plan.element(), fieldSteps(names), views);
        return type == null ? null
                : valuesFor(views.apply(type).shape(), pool).stream()
                        .filter(each -> !each.equals(value)).findFirst().orElse(null);
    }

    /** {@code element} with {@code replacement} at the fields {@code names} below it, or null
     *  where there is no such place in it. */
    private ObservedValue with(ObservedValue element, List<String> names,
                               ObservedValue replacement) {
        return inputs.rewritingBelow(element, plan.element(), fieldSteps(names),
                (_, _, _) -> Stream.of(replacement), views).findFirst().orElse(null);
    }

    /** The values a row holds, by kind, in the order of a walk that does not depend on hashing. */
    private static final class Pool {

        private final Map<Class<?>, Set<ObservedValue>> byKind = new HashMap<>();

        static Pool of(List<ObservedValue> seen) {
            Pool pool = new Pool();
            seen.forEach(pool::gather);
            return pool;
        }

        List<ObservedValue> of(Class<?> kind) {
            return byKind.getOrDefault(kind, Set.of()).stream().limit(MOST_VALUES_OF_A_KIND)
                    .toList();
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
