package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.observe.Figure;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
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
     * what was built, what stands for {@code standing} at it, and where that is a list, a list of
     * one of what stands for its element — or null where the boundary built none at some
     * parameter. The figures the search stopped at are added to
     * {@code stopped}: a value a run's observation was cut short at, and values left untried.
     *
     * @param standing the type whose representatives are tried at each parameter, which is the
     *                 parameter's own where nothing else takes its place
     * @param listing  the element of the list each parameter is, as the reading of the input
     *                 says, or null where it is no list or a list of one is not tried there
     * @param atItsFirst which parameters are tried with their first value alone: the ones a run
     *                 of the behavior does not turn on, since another value of one of them is the
     *                 same run, and the rows of the others are not to be spent on them
     */
    static List<List<Built>> tried(List<Type> types, List<List<FixtureTemplate>> named,
                                   List<List<ObservedValue>> taken, IntFunction<Type> standing,
                                   IntFunction<Type> listing, IntPredicate atItsFirst,
                                   RuleReadingContext reading, Building building,
                                   Set<Figure> stopped) {
        List<List<Built>> each = new ArrayList<>();
        for (int i = 0; i < types.size(); i++) {
            List<FixtureTemplate> tried = new ArrayList<>(named.get(i));
            for (List<ObservedValue> row : taken) {
                // A value the run's observation was cut short at is one the search did not get
                // to try, at that figure.
                if (row.get(i) instanceof ObservedValue.Truncated(Figure cut)) {
                    stopped.add(cut);
                } else if (ObservedFixtures.of(row.get(i), types.get(i), reading)
                        instanceof ObservedFixtures.Writing.Written<FixtureTemplate>(
                                FixtureTemplate fixture)
                        && !tried.contains(fixture)) {
                    tried.add(fixture);
                }
            }
            tried.addAll(Partitions.representativesOf(standing.apply(i), reading).values());
            // And a list of one of what stands for its element: what stands for a list holds
            // nothing, and a walk of nothing gets to no comparison inside it.
            Type element = listing.apply(i);
            if (element != null) {
                for (FixtureTemplate one : Partitions.representativesOf(element, reading).values()) {
                    FixtureTemplate holding = FixtureTemplate.collection(List.of(one));
                    if (!tried.contains(holding)) {
                        tried.add(holding);
                    }
                }
            }
            List<Built> made = new ArrayList<>();
            for (FixtureTemplate one : upTo(tried, stopped)) {
                building.build(i, one).ifPresent(value -> made.add(new Built(one, value)));
            }
            if (made.isEmpty()) {
                return null;
            }
            each.add(atItsFirst.test(i) ? made.subList(0, 1) : made);
        }
        return each;
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
