package souther.compiler.partition;

import souther.compiler.check.RuleReadingContext;
import souther.compiler.observe.Figure;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.Set;
import java.util.function.IntFunction;

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

    /** Whether the behavior answers on a row of these inputs, a run of it going through the
     *  comparison a witness is asked for. */
    public interface Running {
        boolean getsThere(List<FixtureTemplate> inputs);
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
     */
    static List<List<Built>> tried(List<Type> types, List<List<FixtureTemplate>> named,
                                   List<List<ObservedValue>> taken, IntFunction<Type> standing,
                                   IntFunction<Type> listing, RuleReadingContext reading,
                                   Building building, Set<Figure> stopped) {
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
            each.add(made);
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

    /** Rows taking one value of each parameter, nearest first — every parameter at its first
     *  before any at its second — and no more than the search tries, with the figure added to
     *  {@code stopped} where some are left untried. */
    static List<List<Built>> rowsOf(List<List<Built>> each, Set<Figure> stopped) {
        List<List<Built>> out = new ArrayList<>();
        int[] at = new int[each.size()];
        while (true) {
            if (out.size() == MOST_VALUES) {
                stopped.add(CompositionBudget.VALUES_AN_ELEMENT_IS_CHOSEN_AMONG.figure());
                break;
            }
            List<Built> row = new ArrayList<>();
            for (int i = 0; i < each.size(); i++) {
                row.add(each.get(i).get(at[i]));
            }
            out.add(row);
            int moved = 0;
            while (moved < at.length && at[moved] + 1 >= each.get(moved).size()) {
                at[moved] = 0;
                moved++;
            }
            if (moved == at.length) {
                break;
            }
            at[moved]++;
        }
        return out;
    }
}
