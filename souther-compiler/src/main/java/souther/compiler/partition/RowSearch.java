package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.Shape;
import souther.compiler.check.TypeView;
import souther.compiler.observe.Figure;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.function.Function;
import java.util.function.IntFunction;
import java.util.function.IntPredicate;

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
        Function<List<FixtureTemplate>, FixtureTemplate> holding =
                elements -> WornNames.collectionHolding(view, elements, source);
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

    /** {@code one} added where there is room for it and it is not there, and nothing where it
     *  could not be written (null). */
    private static void addOnce(FixtureTemplate one, List<FixtureTemplate> into) {
        if (one != null && hasRoom(into) && !into.contains(one)) {
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
