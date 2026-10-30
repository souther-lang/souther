package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;

import java.util.List;

/**
 * What a search for a row at one item of a border is asked to find, by the way such a row can be
 * found.
 *
 * <p><b>Two ways, because they prove different things.</b> A quantity whose values are a function
 * this compiler reads of the input's numbers says where those numbers have to stand, and a search
 * solves for them ({@link Standing}, {@link LevelRealizer}): what it finds is a row there, and what
 * it finds nowhere the rules may leave nothing at. A number only a run works out says nothing of
 * the input: a row is found by running candidates and reading what the run worked out, which finds
 * a row where one ran there and, where none did, finds that the candidates tried were not it and
 * nothing more.
 *
 * <p>So which of the two a quantity is asked is the quantity's ({@link BorderQuantity#searchGoalAt}),
 * and the solver is never handed a goal it has no constraint for. Held in one type, the solver
 * would learn to run rows, and what its answer that nothing stands there proves would depend on
 * which kind of item it was handed.
 */
public sealed interface PointSearchGoal {

    /** A row whose numbers meet {@code constraint}, which the solver solves for. */
    record ByConstraints(Standing constraint) implements PointSearchGoal {

        public ByConstraints {
            if (constraint == null) {
                throw new IllegalArgumentException("a goal by constraints names them");
            }
        }
    }

    /**
     * A row whose run works out a number on the item {@code where} asks for: found by running
     * candidates and asking each run, never by solving.
     *
     * @param lengths how many each container a candidate is written at holds, one number each
     * @param values  the whole numbers a candidate is written at, outside any container
     * @param where   the item
     */
    record ByObservation(List<NumericTerm.FromOnePosition> lengths,
                         List<NumericTerm.FromOnePosition> values, Criterion where)
            implements PointSearchGoal {

        public ByObservation {
            if (lengths == null || values == null || where == null) {
                throw new IllegalArgumentException("a goal by observation says where candidates"
                        + " are written and which item they are run for");
            }
            lengths = List.copyOf(lengths);
            values = List.copyOf(values);
        }
    }
}
