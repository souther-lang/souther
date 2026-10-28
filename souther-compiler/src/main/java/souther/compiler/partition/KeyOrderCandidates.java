package souther.compiler.partition;

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

import java.util.ArrayList;
import java.util.Arrays;
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
import java.util.function.Supplier;
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
 *
 * <p><b>The order the rewrites are looked at in.</b> What is written is a product — the values the
 * two copies are given, where in the container they are written, in which container, at which
 * field — and a row is looked for by taking the first so many ({@link #MOST_REWRITES_LOOKED_AT},
 * {@link #MOST_CANDIDATES}). So the order is what says what is reached, and it is {@link #roundsOf}:
 * one value against each of the others, in both orders, at one site in the container, in every
 * container and at every field, before that value is paired anywhere else. What a bound cuts is
 * then the later sites in the container and the later values, and no value is left out for
 * coming late among the others, nor a site for coming after many pairs. The values are listed
 * a rank at a time, the first of every case before the second of any, so that a value the decoder
 * refuses is stood in for by the next of its case after every case has had its first. In each
 * round the pairs of values of different cases are taken before the pairs of values of one case.
 *
 * <p>Each bound counts the work where it is done: the values listed ({@link #MOST_CASES_OF_A_SUM},
 * {@link #MOST_VALUES_OF_A_CASE}) and the sites visited ({@link #MOST_SITES_OF_A_CONTAINER}) bound
 * the rounds whether or not a round yields a rewrite; {@link #MOST_REWRITES_LOOKED_AT} the
 * rewrites, counting those the decoder refuses; {@link #MOST_CANDIDATES} those it admits. A value
 * the decoder of its own type refuses is left out of the list, so that no round holds one.
 *
 * <p>What a bound cuts is the end of an order, so every order here that has more than one kind of
 * thing in it takes them in turn and not one kind after the other: the sites ({@link #siteAt}),
 * the fields of a round ({@link #turnsOf}), the values of the cases of a sum, the pairs of
 * different cases and of one case, and the containers a row holds, each given
 * {@link #MOST_TURNS_OF_A_VISIT} turns of a round at a time. Nothing is assumed of how alike the
 * containers of a row are: the one a statement is about may be the last the walk meets.
 */
public final class KeyOrderCandidates {

    /** The most distinct values of one kind that two copies of an element are given between
     *  them. */
    static final int MOST_VALUES_OF_A_KIND = 6;

    /** The most rewrites of one row that are looked at, whether or not the decoder admits them. */
    static final int MOST_REWRITES_LOOKED_AT = 192;

    /** The most cases of a sum that two copies of an element are given between them. Counted
     *  apart from the values of one kind, since a sum has a value for each case and no case is
     *  another's room. */
    static final int MOST_CASES_OF_A_SUM = 12;

    /** The most sites in one container that two copies are written at. The sites of a container
     *  grow as the square of its elements, and a round is visited whether or not it yields a
     *  rewrite, so the rounds are counted here, by the sites they visit. */
    static final int MOST_SITES_OF_A_CONTAINER = 32;

    /** The most turns of a round that one container is given in a visit. A container is given
     *  its turns a few at a time, so that the bound on what is looked at is spread over the
     *  containers a row holds and not used up by the first. */
    static final int MOST_TURNS_OF_A_VISIT = 8;

    /** The most values of one case of a sum that are listed. The first of a case is the one
     *  tried; the others are there for the decoder refusing it. */
    static final int MOST_VALUES_OF_A_CASE = 3;

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
        Pool pool = Pool.of(seen, prim -> composedAt(subject, writing.check(), prim), subject.ruleReading());
        List<List<String>> apart = subject.keptApartAt(plan.container());
        ObservedValue held = seen.get(plan.parameter());
        Admitted admitted = new Admitted(subject, writing);
        // A value the decoder of its own type refuses is left out where the values are listed,
        // before anything is scheduled: every rewrite holding it is refused, and a round that
        // holds one yields nothing and so is not counted by the bound on what is looked at.
        List<List<ObservedValue>> given = plan.targets().stream()
                .map(target -> valuesFor(target.type(), target.fields(), pool,
                        plan.named().getOrDefault(target.fields(), List.of())).stream()
                        .filter(value -> admitted.admits(target, value)).toList())
                .toList();
        Schedule schedule = Schedule.of(given);
        // Three bounds, each counting the work where it is done. The rounds are bounded by the
        // values, the sites and the turns of a visit ({@link #roundsOf}), whether or not a round
        // yields; what is looked at, by the rewrites a round yields, counting those the decoder
        // refuses; and what is run, by those it admits. Counting only the last would let a rule
        // that refuses nearly everything be looked at without end, and counting only what is
        // looked at would let the refused ones use up the rows that are run.
        return roundsOf(schedule.blocks(), mostSitesIn(held)).flatMap(round ->
                        inputs.rewritingBelow(held, inputs.types().get(plan.parameter()),
                                plan.container().steps(),
                                (here, _, _) -> heldTwice(here, schedule, round, apart, pool),
                                views))
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
     * The values of the cases of the sum {@code type}, up to {@link #MOST_CASES_OF_A_SUM} of them
     * in the order the declarations write them, and up to {@link #MOST_VALUES_OF_A_CASE} of each,
     * the first of every case before the second of any. The case is the unit and not the value: a
     * case with many values does not use up the room the others are listed in. A case nothing here
     * writes a value of is left out, which is a case this did not find and not one that cannot be;
     * so is a case past the most, which is not tried. The most is of the cases looked at, in the
     * order the declarations write them, whether or not a value is written of each: a case that
     * has none uses its place.
     *
     * <p>Each value is the case itself, without the names the field wears. The walk that puts the
     * rewritten value back puts those on ({@link BehaviorInputs.Rewrite}), as it does for the
     * values of {@link #scalarValues}.
     */
    private List<ObservedValue> casesOf(Type type, List<String> fields, Pool pool) {
        return pool.casesAt(List.of(type, fields), () -> writeCasesOf(type, fields, pool));
    }

    private List<ObservedValue> writeCasesOf(Type type, List<String> fields, Pool pool) {
        TypeView view = views.apply(type);
        if (!(view.shape() instanceof Shape.Sum sum)) {
            return List.of();
        }
        TermPath at = plan.container().element();
        for (String each : fields) {
            at = at.then(each);
        }
        TermPath inCase = at;
        List<List<ObservedValue>> ofEachCase = sum.reaches().cases().stream()
                .limit(MOST_CASES_OF_A_SUM)
                .map(leaf -> ValuesOfAnElement.of(Type.ref(leaf), inCase, pool.reading(),
                        MOST_VALUES_OF_A_CASE,
                        (_, held) -> held.shape() instanceof Shape.Scalar scalar
                                ? scalarValues(scalar, pool, List.of()) : null))
                .filter(listed -> listed != null && !listed.values().isEmpty())
                .map(ValuesOfAnElement.Listed::values)
                .toList();
        // The first of every case, then the second of every case that has one: the order the
        // rounds take the values in, so that the case the decoder refused the first value of is
        // stood in for after each case has been given its first.
        List<ObservedValue> out = new ArrayList<>();
        for (int rank = 0; rank < MOST_VALUES_OF_A_CASE; rank++) {
            for (List<ObservedValue> ofTheCase : ofEachCase) {
                if (rank < ofTheCase.size()) {
                    out.add(ofTheCase.get(rank));
                }
            }
        }
        return out;
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

    /** What a composer would write at a scalar type, as the values an observation holds: what the
     *  type's own decoder makes of each value it offers. */
    private static List<ObservedValue> composedAt(MeasuredInput subject,
                                                  Generator.CandidateCheck check, Type.Prim prim) {
        List<ObservedValue> out = new ArrayList<>();
        for (FixtureTemplate each : subject.representativesHolding(prim,
                FieldDomains.ConstructionLimits.NONE).values()) {
            check.builtAlone(prim, each).filter(value -> !out.contains(value))
                    .ifPresent(out::add);
        }
        return out;
    }

    /**
     * What the container comes to with a key held twice, one rewrite at a time: for each field,
     * the pairs of values {@code round} names, written at the place it names in the container.
     * Called for each container the walk meets, and gives each of them the turns of the round's
     * visit and no more, so that the next container is given its own before the bound on what is
     * looked at is used up by the one before.
     */
    private Stream<ObservedValue> heldTwice(ObservedValue here, Schedule schedule, Round round,
                                            List<List<String>> apart, Pool pool) {
        if (!(here instanceof ObservedValue.Sequence(List<ObservedValue> elements))
                || elements.isEmpty()) {
            return Stream.empty();
        }
        Site site = siteAt(elements.size(), round.site());
        if (site == null) {
            return Stream.empty();
        }
        return visitOf(schedule.turns().get(round.value()), round.block()).stream()
                .map(turn -> {
                    Pair pair = schedule.pairs().get(round.value()).get(turn.of()).get(turn.at());
                    List<ObservedValue> values = schedule.given().get(turn.of());
                    return written(site, elements, plan.targets().get(turn.of()),
                            values.get(pair.earlier()), values.get(pair.later()), apart, pool);
                })
                .filter(Objects::nonNull);
    }

    /**
     * What the rounds are made of: the values each field is given, the pairs of each value's round
     * for each field, and the turns the fields take them in. Worked out once for a row.
     */
    private record Schedule(List<List<ObservedValue>> given, List<List<List<Pair>>> pairs,
                            List<List<Turn>> turns) {

        static Schedule of(List<List<ObservedValue>> given) {
            int most = given.stream().mapToInt(List::size).max().orElse(0);
            List<List<List<Pair>>> pairs = new ArrayList<>();
            List<List<Turn>> turns = new ArrayList<>();
            for (int value = 0; value < Math.max(0, most - 1); value++) {
                List<List<Pair>> ofTheFields = new ArrayList<>();
                for (List<ObservedValue> values : given) {
                    ofTheFields.add(pairsOfRound(values, value));
                }
                pairs.add(ofTheFields);
                turns.add(turnsOf(ofTheFields.stream().mapToInt(List::size).toArray()));
            }
            return new Schedule(given, pairs, turns);
        }

        /** How many visits the round of each value is made of. */
        int[] blocks() {
            return turns.stream().mapToInt(each -> blocksOf(each.size())).toArray();
        }
    }

    /** The turns of the {@code block}-th visit of a round: {@link #MOST_TURNS_OF_A_VISIT} of them,
     *  fewer at the end, none past it. */
    static List<Turn> visitOf(List<Turn> turns, int block) {
        int from = Math.min(block * MOST_TURNS_OF_A_VISIT, turns.size());
        return turns.subList(from, Math.min(from + MOST_TURNS_OF_A_VISIT, turns.size()));
    }

    /** How many visits {@code turns} turns are made of, a visit being
     *  {@link #MOST_TURNS_OF_A_VISIT} of them. */
    static int blocksOf(int turns) {
        return (turns + MOST_TURNS_OF_A_VISIT - 1) / MOST_TURNS_OF_A_VISIT;
    }

    /** The {@code at}-th pair of the {@code of}-th field of a round. */
    record Turn(int of, int at) {}

    /**
     * The order the fields of a round take their pairs in, one pair of each in turn: a field with
     * many pairs does not use up the bound on what is looked at before a field with few is given
     * its first.
     *
     * @param counts how many pairs each field has in the round
     */
    static List<Turn> turnsOf(int[] counts) {
        List<Turn> out = new ArrayList<>();
        int most = Arrays.stream(counts).max().orElse(0);
        for (int at = 0; at < most; at++) {
            for (int of = 0; of < counts.length; of++) {
                if (at < counts[of]) {
                    out.add(new Turn(of, at));
                }
            }
        }
        return out;
    }

    /**
     * Where two copies are written in a container: an element given the key of an earlier one,
     * or an element held again.
     */
    sealed interface Site {

        /** Two of the elements, the later given the key of the earlier. */
        record Overwriting(int first, int second) implements Site {}

        /** One element, held again beside itself. */
        record Repeating(int at) implements Site {}
    }

    /** One value to be given, paired with another: the index of the value the earlier copy is
     *  given and of the one the later copy is. */
    record Pair(int earlier, int later) {}

    /** What a bound cuts last: the sites in the container come one at a time, within a value, and
     *  the turns of a round a visit at a time, within a site. */
    record Round(int value, int site, int block) {}

    /**
     * How many sites two copies are written at in a container of {@code size} elements: each
     * element held again, and each pair of elements.
     */
    static int sitesIn(int size) {
        long elements = size;
        return (int) Math.min(elements + elements * (elements - 1) / 2, Integer.MAX_VALUE);
    }

    /**
     * The site of rank {@code rank} in a container of {@code size} elements, or null past the
     * last: an element held again and a pair of elements in turn, the one kind continuing alone
     * once the other has none left. The two kinds are taken alternately because a bound on how many
     * sites are visited cuts the end of the order, and one kind taken before the other would be
     * cut whole: the elements held again change how many elements there are, which a rule on the
     * length refuses, and the pairs do not. Worked out from the rank and not listed, since a
     * container is asked for the site of every round.
     */
    static Site siteAt(int size, int rank) {
        if (rank < 0 || rank >= sitesIn(size)) {
            return null;
        }
        long repeats = size;
        long pairs = repeats * (repeats - 1) / 2;
        long inTurn = Math.min(repeats, pairs);
        if (rank < 2 * inTurn) {
            return rank % 2 == 0 ? new Site.Repeating(rank / 2) : overwritingAt(size, rank / 2);
        }
        long alone = rank - inTurn;
        return repeats > pairs ? new Site.Repeating((int) alone)
                : overwritingAt(size, (int) alone);
    }

    /** The pair of elements of that index, the pairs taken by the first element and then the
     *  second. */
    private static Site overwritingAt(int size, int index) {
        int left = index;
        for (int first = 0; first < size - 1; first++) {
            int pairs = size - 1 - first;
            if (left < pairs) {
                return new Site.Overwriting(first, first + 1 + left);
            }
            left -= pairs;
        }
        return null;
    }

    /**
     * The value {@code value} against each later one, in both orders: the pairs of the round of
     * that value.
     */
    static List<Pair> pairsWith(int values, int value) {
        List<Pair> out = new ArrayList<>();
        for (int other = value + 1; other < values; other++) {
            out.add(new Pair(value, other));
            out.add(new Pair(other, value));
        }
        return out;
    }

    /**
     * The rounds the rewrites are looked at in: a value is taken against every other, in both
     * orders, at the first site in the container, then at the second, and so on, before the next
     * value is taken against those after it.
     *
     * <p>What tells the two ways round the order apart is a value the statement comes out one way
     * on and another it comes out the other way on, and a value is on one side of any such line
     * unless the statement is the same at every value after it. So every line is reached in the
     * rounds of the first value that has one after it — {@code 2 × (values − 1)} pairs for each
     * site — and what a bound cuts is the later sites and the later values. The sites are the
     * outer of the two, since a site left out costs a position of the container and a value left
     * out costs a case.
     *
     * <p>A round is visited container by container, and a container is given
     * {@link #MOST_TURNS_OF_A_VISIT} of its turns in a visit: a round of many turns is then made of
     * several visits, and each container is given its first before any is given its second. A
     * container taken whole would use up the bound on what is looked at before the next was
     * reached, and the one a statement is about may be the next.
     *
     * @param blocks the visits the round of each value is made of, the first value first
     * @param sites  the most sites any container has, of which the first
     *               {@link #MOST_SITES_OF_A_CONTAINER} are visited
     */
    static Stream<Round> roundsOf(int[] blocks, int sites) {
        int most = Math.min(sites, MOST_SITES_OF_A_CONTAINER);
        return IntStream.range(0, blocks.length).boxed().flatMap(value ->
                IntStream.range(0, most).boxed().flatMap(site ->
                        IntStream.range(0, blocks[value])
                                .mapToObj(block -> new Round(value, site, block))));
    }

    /** The most sites any container in {@code held} has. */
    private int mostSitesIn(ObservedValue held) {
        int[] most = {0};
        inputs.rewritingBelow(held, inputs.types().get(plan.parameter()),
                plan.container().steps(), (here, _, _) -> {
                    if (here instanceof ObservedValue.Sequence(List<ObservedValue> elements)) {
                        most[0] = Math.max(most[0], sitesIn(elements.size()));
                    }
                    return Stream.empty();
                }, views).forEach(_ -> { });
        return most[0];
    }

    /**
     * The pairs of one round: {@link #pairsWith(int, int)} of the value, the pairs of different
     * cases of a sum first and then the pairs of one case. Both are in every round, so a bound on
     * what is looked at cuts later rounds, and not one kind of pair for coming after the other
     * kind in every round.
     */
    static List<Pair> pairsOfRound(List<ObservedValue> values, int value) {
        List<Pair> out = new ArrayList<>(pairsWith(values, value, false));
        out.addAll(pairsWith(values, value, true));
        return out;
    }

    /**
     * The pairs of {@link #pairsWith(int, int)} whose two values are of one case of a sum, or of
     * different cases, as {@code ofOneCase} says. The two between them are every pair.
     */
    static List<Pair> pairsWith(List<ObservedValue> values, int value, boolean ofOneCase) {
        return pairsWith(values.size(), value).stream()
                .filter(pair -> ofOneCase == ofOneCase(values.get(pair.earlier()),
                        values.get(pair.later())))
                .toList();
    }

    /**
     * Whether the values are of one case of a sum. Two copies of a key given two values of one
     * case tell the order apart where the statement reads what the case holds, and are tried
     * after the pairs of different cases in each round: those are the ones a sum is given its
     * cases for, and the others are the more of them for a statement that reads the payload.
     */
    private static boolean ofOneCase(ObservedValue one, ObservedValue other) {
        return one instanceof ObservedValue.Constructed first
                && other instanceof ObservedValue.Constructed second
                && first.type().equals(second.type());
    }

    private ObservedValue written(Site site, List<ObservedValue> elements, Target target,
                                  ObservedValue earlier, ObservedValue later,
                                  List<List<String>> apart, Pool pool) {
        return switch (site) {
            case Site.Overwriting(int first, int second) ->
                    overwritten(elements, first, second, target, earlier, later);
            case Site.Repeating(int at) ->
                    repeated(elements, at, target, earlier, later, apart, pool);
        };
    }

    /**
     * Two of the elements, the later given the key of the earlier and the two given the values
     * between them. Everything else each held stays, so a field that must differ between
     * elements, and the number of elements, are as they were.
     */
    private ObservedValue overwritten(List<ObservedValue> elements, int first, int second,
                                      Target target, ObservedValue earlier, ObservedValue later) {
        ObservedValue key = inputs.readingAt(elements.get(first), plan.element(), plan.key(),
                views);
        ObservedValue keyed = key == null ? null : with(elements.get(second), plan.key(), key);
        ObservedValue one = with(elements.get(first), target.fields(), earlier);
        ObservedValue other = keyed == null ? null : with(keyed, target.fields(), later);
        if (one == null || other == null) {
            return null;
        }
        List<ObservedValue> held = new ArrayList<>(elements);
        held.set(first, one);
        held.set(second, other);
        return new ObservedValue.Sequence(held);
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
    private ObservedValue repeated(List<ObservedValue> elements, int at, Target target,
                                   ObservedValue earlier, ObservedValue later,
                                   List<List<String>> apart, Pool pool) {
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
        return other == null ? null : new ObservedValue.Sequence(held);
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

    /**
     * Whether the type of a field refuses a value on its own, asked of the decoder of that type
     * ({@link Generator.CandidateCheck#admissibility}) and of nothing beside it. A value it refuses
     * is refused in every rewrite that holds it, and a rewrite refused is counted against the
     * bound on those looked at ({@link #MOST_REWRITES_LOOKED_AT}) before the decoder says so, so
     * the value is left out before that.
     *
     * <p>Only that. A value the type admits can still be refused beside the others, by a rule
     * relating two fields or the elements of the container, and such a value is kept: the
     * rewrites that hold it are refused, or not, by the decoder of the whole.
     *
     * <p>Asked once of each value of each field, so at most as many times as values are listed.
     */
    private final class Admitted {

        private final MeasuredInput subject;
        private final RowWriting writing;
        private final Map<List<Object>, Boolean> known = new HashMap<>();

        Admitted(MeasuredInput subject, RowWriting writing) {
            this.subject = subject;
            this.writing = writing;
        }

        boolean admits(Target target, ObservedValue value) {
            return known.computeIfAbsent(List.of(target.type(), value), _ -> asked(target, value));
        }

        private boolean asked(Target target, ObservedValue value) {
            // As the position wears it: the names the field's type wears go on once, here.
            ObservedValue worn = ObservedValue.wrapped(views.apply(target.type()).wrappers(),
                    value);
            return switch (ObservedFixtures.of(worn, target.type(), subject.ruleReading())) {
                case ObservedFixtures.Writing.Written<FixtureTemplate>(var written) ->
                        !refusedOnItsOwn(writing.check(), target.type(), written);
                case ObservedFixtures.Writing.NotWritable<FixtureTemplate> _ -> false;
            };
        }
    }

    /**
     * Whether the decoder of {@code type} refuses {@code value} on its own: what is refused so is
     * refused in every value it could be put in. Not whether the whole is refused with it put in
     * ({@link Generator.CandidateCheck#build}), which a rule relating the elements decides and
     * which says nothing of the value.
     */
    static boolean refusedOnItsOwn(Generator.CandidateCheck check, Type type,
                                   FixtureTemplate value) {
        return check.admissibility(type, value)
                == Generator.CandidateCheck.Admissibility.REFUSED;
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

        private final Map<List<Object>, List<ObservedValue>> cases = new HashMap<>();

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

        /** The cases of a sum written at one place, worked out once for the row: the container
         *  is rewritten once per element and the place is the same each time. */
        List<ObservedValue> casesAt(List<Object> place, Supplier<List<ObservedValue>> written) {
            return cases.computeIfAbsent(place, _ -> written.get());
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
