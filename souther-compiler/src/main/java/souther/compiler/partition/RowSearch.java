package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.inputs.TermPath;
import souther.compiler.observe.Figure;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.function.IntFunction;
import java.util.function.IntPredicate;
import java.util.function.Predicate;

/**
 * The rows of a behavior's inputs a search for a witness tries, nearest first, each value built
 * by the boundary: a named value of a parameter's type the model writes ({@code TypedFixtureValues}),
 * what each row written for the behavior took, and what stands for the type
 * ({@link Partitions#representativesOf}). A value the boundary refuses is no value of the row.
 *
 * <p>Which rows are tried is a search and claims nothing: what a witness claims is what was
 * built of its row and what a run of it did, which the reader of each kind of witness asks
 * ({@link CountWitnesses}, {@link ReachWitnesses}). A row the search did not try is no row shown
 * not to exist, and the figure it stopped at says how far it went.
 */
public final class RowSearch {

    /** How many of a parameter's values, and how many rows, are tried before the search stops. */
    static final int MOST_VALUES = CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG.maximum();

    private RowSearch() {}

    /** What the boundary builds of one input at a parameter, or empty where it refuses it. */
    public interface Building {
        Optional<ObservedValue> build(int parameter, FixtureTemplate fixture);
    }

    /** What a run of the behavior on a row of these inputs came to: whether it answered going
     *  through the comparison a witness is asked for, and where it stopped where it did. */
    public interface Running {
        Run run(List<FixtureTemplate> inputs);
    }

    /**
     * What one run came to.
     *
     * <p>Two facts and not one, since a run that answered somewhere else and a run that stopped are
     * both no witness, and only the second is an input the model has not decided about.
     *
     * @param getsThere whether it answered, going through the comparison
     * @param stopped   where it stopped without answering, where it did; none where it answered
     */
    public record Run(boolean getsThere, Optional<WhereARunStopped> stopped) {

        /** A run that answered, or one nothing ran, which stopped nowhere. */
        public static Run stoppedNowhere(boolean getsThere) {
            return new Run(getsThere, Optional.empty());
        }

        public Run {
            Objects.requireNonNull(stopped, "a run stopped somewhere or nowhere");
            if (getsThere && stopped.isPresent()) {
                throw new IllegalArgumentException("a run that answered did not stop: " + stopped);
            }
        }
    }

    /** One input the boundary built, and the fixture it was built of. */
    record Built(FixtureTemplate fixture, ObservedValue value) {}

    /**
     * The values each parameter is tried with, built, in the order they are tried: what the model
     * names at its type, what each row written for the behavior took there, written back from
     * what was built, what stands for {@code standing} at it, and where {@code holdingOne} says so
     * and it is a collection, one holding one of what stands for what it holds — or null where the
     * boundary built none at some parameter. The figures the search stopped at are added to
     * {@code stopped}: a value a run's observation was cut short at, and values left untried.
     *
     * @param standing the type whose representatives are tried at each parameter, which is the
     *                 parameter's own where nothing else takes its place
     * @param atItsFirst which parameters are tried with their first value alone: the ones a run
     *                 of the behavior does not turn on, since another value of one of them is the
     *                 same run, and the rows of the others are not to be spent on them
     * @param holdingOne which parameters are tried holding one of what stands for what they hold
     *                 as well, where they are collections: what stands for a collection holds
     *                 nothing, and a walk of nothing gets to no comparison inside it, nor a
     *                 statement read a place in
     */
    static List<List<Built>> tried(List<Type> types, List<List<FixtureTemplate>> named,
                                   List<List<ObservedValue>> taken, IntFunction<Type> standing,
                                   IntPredicate holdingOne, IntPredicate atItsFirst,
                                   RuleReadingContext reading, Building building,
                                   Set<Figure> stopped) {
        return tried(types, named, taken, standing, holdingOne, atItsFirst, _ -> List.of(), reading,
                building, stopped);
    }

    /**
     * The same, with {@code aimed} the values a parameter is tried with besides, the collections
     * in them holding what the conditions on the way to the comparison ask of them
     * ({@link #aimedAt}): after what stands for the parameter and before what holds one of what
     * stands for what the parameter holds, so that a value made for what is asked is tried before
     * the values that were made for nothing in particular.
     */
    static List<List<Built>> tried(List<Type> types, List<List<FixtureTemplate>> named,
                                   List<List<ObservedValue>> taken, IntFunction<Type> standing,
                                   IntPredicate holdingOne, IntPredicate atItsFirst,
                                   IntFunction<List<FixtureTemplate>> aimed,
                                   RuleReadingContext reading, Building building,
                                   Set<Figure> stopped) {
        List<List<Built>> each = new ArrayList<>();
        for (int i = 0; i < types.size(); i++) {
            if (atItsFirst.test(i)) {
                // Its first value the boundary builds and nothing past it: another value of it is
                // the same run, so none is built, and none is a figure the search stopped at.
                Built first = firstBuilt(i, types, named, taken, standing, holdingOne, reading,
                        building, stopped);
                if (first == null) {
                    return null;
                }
                each.add(List.of(first));
                continue;
            }
            List<FixtureTemplate> tried = new ArrayList<>(named.get(i));
            takenAt(i, types.get(i), taken, reading, tried, stopped);
            tried.addAll(Partitions.representativesOf(standing.apply(i), reading).values());
            for (FixtureTemplate one : aimed.apply(i)) {
                addOnce(one, tried);
            }
            if (holdingOne.test(i)) {
                addHoldingOne(types.get(i), reading, tried);
            }
            List<Built> made = new ArrayList<>();
            for (FixtureTemplate one : upTo(tried, stopped)) {
                building.build(i, one).ifPresent(value -> made.add(new Built(one, value)));
            }
            if (made.isEmpty()) {
                return null;
            }
            each.add(made);
        }
        return each;
    }

    /**
     * The first value at {@code parameter} the boundary builds, going through what the model
     * names, what the rows took, what stands for the type and a list of one of what stands for its
     * element, each only as far as it takes to find one; or null where none is built.
     *
     * <p>No more than {@link #MOST_VALUES} are built in looking, which is the figure the values of
     * a parameter are tried to: past it the figure is added to {@code stopped}, and there is
     * nothing to say where one was found first.
     */
    private static Built firstBuilt(int parameter, List<Type> types,
                                    List<List<FixtureTemplate>> named,
                                    List<List<ObservedValue>> taken, IntFunction<Type> standing,
                                    IntPredicate holdingOne, RuleReadingContext reading,
                                    Building building, Set<Figure> stopped) {
        int[] left = {MOST_VALUES};
        // Values a run's observation was cut short at: said only where no value is found, since a
        // value that was found makes what was not tried of no account to what is tried with.
        Set<Figure> cut = new HashSet<>();
        List<FixtureTemplate> stage = new ArrayList<>(named.get(parameter));
        Built built = firstOf(parameter, stage, building, left, stopped);
        if (built == null) {
            stage = new ArrayList<>();
            takenAt(parameter, types.get(parameter), taken, reading, stage, cut);
            built = firstOf(parameter, stage, building, left, stopped);
        }
        if (built == null) {
            built = firstOf(parameter, List.copyOf(
                    Partitions.representativesOf(standing.apply(parameter), reading).values()),
                    building, left, stopped);
        }
        if (built == null) {
            stage = new ArrayList<>();
            if (holdingOne.test(parameter)) {
                addHoldingOne(types.get(parameter), reading, stage);
            }
            built = firstOf(parameter, stage, building, left, stopped);
        }
        if (built == null) {
            stopped.addAll(cut);
        }
        return built;
    }

    /** The first of {@code candidates} the boundary builds, spending from {@code left} one for
     *  each it is asked to build; null where none is built or {@code left} ran out, which is said
     *  as the figure. */
    private static Built firstOf(int parameter, List<FixtureTemplate> candidates,
                                 Building building, int[] left, Set<Figure> stopped) {
        for (FixtureTemplate one : candidates) {
            if (left[0] <= 0) {
                stopped.add(CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG.figure());
                return null;
            }
            left[0]--;
            Optional<ObservedValue> value = building.build(parameter, one);
            if (value.isPresent()) {
                return new Built(one, value.get());
            }
        }
        return null;
    }

    /** Adds to {@code into} what each row took at {@code parameter}, written back from what was
     *  built, each once; and to {@code stopped} the figure a value a run's observation was cut
     *  short at is one the search did not get to try. */
    private static void takenAt(int parameter, Type type, List<List<ObservedValue>> taken,
                                RuleReadingContext reading, List<FixtureTemplate> into,
                                Set<Figure> stopped) {
        for (List<ObservedValue> row : taken) {
            if (row.get(parameter) instanceof ObservedValue.Truncated(Figure cut)) {
                stopped.add(cut);
            } else if (ObservedFixtures.of(row.get(parameter), type, reading)
                    instanceof ObservedFixtures.Writing.Written<FixtureTemplate>(
                            FixtureTemplate fixture)
                    && !into.contains(fixture)) {
                into.add(fixture);
            }
        }
    }

    /**
     * Adds to {@code into} what holds one of what stands for what {@code type} holds, where it is
     * a collection: one of what stands for its element, or one entry of what stand for its key and
     * its value, each once.
     */
    private static void addHoldingOne(Type type, RuleReadingContext reading,
                                      List<FixtureTemplate> into) {
        RuleReadingSource source = reading.source();
        TypeView view = TypeView.of(type, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        // Whether the names can be written is the type's, so it is asked once and not after every
        // candidate: a type whose names cannot be written has no candidate to enumerate.
        if (!(WornNames.of(view.wrappers(), source) instanceof WornNames.Spelled spelled)) {
            return;
        }
        Function<List<FixtureTemplate>, FixtureTemplate> holding = spelled::holding;
        switch (view.shape()) {
            case Shape.Sequence sequence -> addEachHoldingOne(
                    Partitions.representativesOf(sequence.element(), reading).values(), holding,
                    into);
            case Shape.Mapping mapping -> addEachHoldingOneEntry(
                    Partitions.representativesOf(mapping.key(), reading).values(),
                    Partitions.representativesOf(mapping.value(), reading).values(), holding,
                    into);
            default -> { }
        }
    }

    /**
     * What a value of {@code type}, the type of the parameter {@code parameter}, is where the
     * collections {@code aims} name in it hold the numbers they are asked to, the rest of the
     * value composed under the rules relating the fields. The stops met in composing go to
     * {@code stopped}, as a value not built for one is not a value that cannot be built.
     *
     * <p>First the values that meet every aim of the parameter at once, each taking a number of
     * each aim's, the nearest to where its condition turns first: a parameter whose two collections
     * are each asked to total off nought is not answered by a value that makes one of them so, and
     * which number each takes is no fixed pairing, since the rules relating the fields may allow
     * only some — two totals held to add up to nought are met at one and its opposite. Then each
     * aim alone, which is what is left where the others cannot be met together.
     *
     * <p>Every value composed is a try against {@link #MOST_VALUES}, whether it comes to a value
     * or not, and the figure is added to {@code stopped} where it runs out with ways left: a
     * record of many collections has more ways to hold a number in each than are tried.
     */
    static List<FixtureTemplate> aimedAt(String parameter, Type type, List<RowAims.Aim> aims,
                                         RuleReadingContext reading, Set<Figure> stopped) {
        List<RowAims.Aim> ofIt = aims.stream()
                .filter(aim -> aim.container().head().equals(parameter)).toList();
        List<FixtureTemplate> out = new ArrayList<>();
        int[] left = {MOST_VALUES};
        Tried[] ended = {Tried.GO_ON};
        if (ofIt.size() > 1) {
            nearestFirst(ofIt, picks -> {
                List<Held> together = new ArrayList<>();
                for (int at = 0; at < ofIt.size(); at++) {
                    RowAims.Aim aim = ofIt.get(at);
                    together.add(new Held(aim.container().steps(),
                            aim.elements().get(picks[at])));
                }
                ended[0] = tried(left, type, together, reading, stopped, out);
                return ended[0] == Tried.GO_ON;
            });
        }
        for (RowAims.Aim aim : ofIt) {
            for (BigInteger number : aim.elements()) {
                if (ended[0] != Tried.GO_ON) {
                    break;
                }
                ended[0] = tried(left, type, List.of(new Held(aim.container().steps(), number)),
                        reading, stopped, out);
            }
        }
        if (ended[0] == Tried.CUT) {
            stopped.add(CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG.figure());
        }
        return out;
    }

    /** Whether the search of the values an aim asks for goes on. */
    private enum Tried { GO_ON, ENOUGH, CUT }

    /** One value composed with the collections {@code held} holding their numbers, if one is, as a
     *  try against {@code left}. */
    private static Tried tried(int[] left, Type type, List<Held> held, RuleReadingContext reading,
                               Set<Figure> stopped, List<FixtureTemplate> into) {
        if (!hasRoom(into)) {
            return Tried.ENOUGH;
        }
        if (left[0] == 0) {
            return Tried.CUT;
        }
        left[0]--;
        FixtureTemplate value = holdingAt(type, held, reading, stopped);
        if (value != null) {
            addOnce(value, into);
        }
        return Tried.GO_ON;
    }

    /**
     * Each way of taking one number of each of {@code aims}, as the places of the numbers taken, the
     * ways nearest to every first number first: by what the places add up to, and then in the order
     * the aims stand in. Made one at a time and no further than {@code each} goes on, since the ways
     * are as many as the numbers of each multiplied.
     */
    static void nearestFirst(List<RowAims.Aim> aims, Predicate<int[]> each) {
        int[] farthest = new int[aims.size() + 1];
        for (int at = aims.size() - 1; at >= 0; at--) {
            farthest[at] = farthest[at + 1] + aims.get(at).elements().size() - 1;
        }
        int[] picks = new int[aims.size()];
        for (int sum = 0; sum <= farthest[0]; sum++) {
            if (!takingNumbers(aims, 0, sum, picks, farthest, each)) {
                return;
            }
        }
    }

    /** The ways of taking a number of each aim from {@code at} on whose places add up to
     *  {@code rest}; whether {@code each} went on through all of them. */
    private static boolean takingNumbers(List<RowAims.Aim> aims, int at, int rest, int[] picks,
                                         int[] farthest, Predicate<int[]> each) {
        if (at == aims.size()) {
            return each.test(picks);
        }
        int most = Math.min(rest, aims.get(at).elements().size() - 1);
        for (int place = 0; place <= most; place++) {
            if (rest - place > farthest[at + 1]) {
                continue;
            }
            picks[at] = place;
            if (!takingNumbers(aims, at + 1, rest - place, picks, farthest, each)) {
                return false;
            }
        }
        return true;
    }

    /** A collection reached by fields {@code steps} down from a position, and the number it is to
     *  hold alone. */
    private record Held(List<TermPath.Step> steps, BigInteger number) {}

    /** A value of {@code type} whose collections {@code held} each hold their number alone, or
     *  null where none is built. */
    private static FixtureTemplate holdingAt(Type type, List<Held> held, RuleReadingContext reading,
                                             Set<Figure> stopped) {
        RuleReadingSource source = reading.source();
        TypeView view = TypeView.of(type, source.inners(), source.symbols(), source.kinds(),
                source.sums());
        if (held.size() == 1 && held.getFirst().steps().isEmpty()) {
            if (!(view.shape() instanceof Shape.Sequence sequence)
                    || !(WornNames.of(view.wrappers(), source) instanceof WornNames.Spelled spelled)) {
                return null;
            }
            FixtureTemplate element = Partitions.writtenNumberAt(sequence.element(),
                    new BigDecimal(held.getFirst().number()), reading);
            return element == null ? null : spelled.holding(List.of(element));
        }
        if (!(view.shape() instanceof Shape.Product(TypeSymbol.AtModule record, var fields))) {
            return null;
        }
        Map<String, List<Held>> byField = new LinkedHashMap<>();
        for (Held each : held) {
            if (each.steps().isEmpty()
                    || !(each.steps().getFirst() instanceof TermPath.Step.Field(String name))) {
                return null;
            }
            byField.computeIfAbsent(name, _ -> new ArrayList<>()).add(new Held(
                    each.steps().subList(1, each.steps().size()), each.number()));
        }
        Map<String, FixtureTemplate> given = new LinkedHashMap<>();
        for (Map.Entry<String, List<Held>> field : byField.entrySet()) {
            FixtureTemplate inner = fields.get(field.getKey()) instanceof Type fieldType
                    ? holdingAt(fieldType, field.getValue(), reading, stopped) : null;
            if (inner == null) {
                return null;
            }
            given.put(field.getKey(), inner);
        }
        Proposals made = Partitions.composed(record,
                Partitions.rulesOver(view.wrappers(), record, source), reading, Set.of(), given,
                Partitions.RulesAround.NONE);
        for (CompositionBudget met : made.met().figures()) {
            stopped.add(met.figure());
        }
        return made.isEmpty() ? null
                : WornNames.under(view.wrappers(), made.values().getFirst(), source);
    }

    /** Adds to {@code into} what {@code holding} makes of each of {@code elements} alone — a
     *  collection of the type, under the names it wears — each once, as far as there is room
     *  ({@link #hasRoom}). */
    static void addEachHoldingOne(List<FixtureTemplate> elements,
                                  Function<List<FixtureTemplate>, FixtureTemplate> holding,
                                  List<FixtureTemplate> into) {
        for (FixtureTemplate one : elements) {
            if (!hasRoom(into)) {
                return;
            }
            addOnce(holding.apply(List.of(one)), into);
        }
    }

    /** Adds to {@code into} what {@code holding} makes of the entry of each key and each value,
     *  each once, as far as there is room ({@link #hasRoom}): the pairs are made one at a time,
     *  and none is made past the room. */
    static void addEachHoldingOneEntry(List<FixtureTemplate> keys, List<FixtureTemplate> values,
                                       Function<List<FixtureTemplate>, FixtureTemplate> holding,
                                       List<FixtureTemplate> into) {
        for (FixtureTemplate key : keys) {
            for (FixtureTemplate value : values) {
                if (!hasRoom(into)) {
                    return;
                }
                addOnce(holding.apply(List.of(FixtureTemplate.entry(key, value))), into);
            }
        }
    }

    /** {@code one} added where there is room for it and it is not there. */
    private static void addOnce(FixtureTemplate one, List<FixtureTemplate> into) {
        if (hasRoom(into) && !into.contains(one)) {
            into.add(one);
        }
    }

    /**
     * Whether one more candidate is worth building: the search tries {@link #MOST_VALUES} of them
     * and one past that says the figure was passed ({@link #upTo}), so a producer stops building
     * where this is false, and the figure is said by what it handed on.
     */
    static boolean hasRoom(List<?> candidates) {
        return candidates.size() <= MOST_VALUES;
    }

    /** As many of {@code values} as the search tries, first first, with the figure added to
     *  {@code stopped} where some are left untried. */
    static <T> List<T> upTo(List<T> values, Set<Figure> stopped) {
        if (values.size() <= MOST_VALUES) {
            return values;
        }
        stopped.add(CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG.figure());
        return values.subList(0, MOST_VALUES);
    }

    /**
     * Rows taking one value of each parameter, nearest first, and no more than the search tries,
     * with the figure added to {@code stopped} where some are left untried.
     *
     * <p>Nearest is how far the values taken are from each parameter's first, added up: the row
     * of every parameter at its first, then each row with one parameter at its second, and so on a
     * step at a time. A row that needs one parameter at its fifth value and the others at their
     * first is among the first rows however many values the others have; taken a parameter at a time
     * in turn, as many values at the first parameter as there are rows to try would leave the rest
     * at their firsts, and a parameter the question does not read would decide which of the others
     * are ever tried.
     */
    static List<List<Built>> rowsOf(List<List<Built>> each, Set<Figure> stopped) {
        List<List<Built>> out = new ArrayList<>();
        int farthest = 0;
        for (List<Built> values : each) {
            farthest += values.size() - 1;
        }
        for (int distance = 0; distance <= farthest; distance++) {
            if (!rowsAt(each, distance, out, stopped)) {
                break;
            }
        }
        return out;
    }

    /**
     * The rows whose values are {@code distance} from the firsts in all, added to {@code out}
     * while there is room for them; false where there was not.
     *
     * <p>The first parameter's value slowest, one parameter after another with the distance it
     * leaves for the rest. Walked with the depth held in an array and not in calls, so that how
     * many parameters a behavior takes is no depth of the stack.
     */
    private static boolean rowsAt(List<List<Built>> each, int distance, List<List<Built>> out,
                                  Set<Figure> stopped) {
        int parameters = each.size();
        int[] at = new int[parameters];
        int[] left = new int[parameters + 1];
        left[0] = distance;
        int depth = 0;
        if (parameters > 0) {
            at[0] = -1;
        }
        while (depth >= 0) {
            if (depth == parameters) {
                if (left[depth] == 0) {
                    if (out.size() == MOST_VALUES) {
                        stopped.add(CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG.figure());
                        return false;
                    }
                    List<Built> row = new ArrayList<>();
                    for (int i = 0; i < parameters; i++) {
                        row.add(each.get(i).get(at[i]));
                    }
                    out.add(row);
                }
                depth--;
                continue;
            }
            at[depth]++;
            if (at[depth] > Math.min(left[depth], each.get(depth).size() - 1)) {
                depth--;
                continue;
            }
            left[depth + 1] = left[depth] - at[depth];
            depth++;
            if (depth < parameters) {
                at[depth] = -1;
            }
        }
        return true;
    }
}
