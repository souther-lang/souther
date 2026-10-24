package souther.compiler.partition;

import souther.compiler.meaning.Proposition;

import java.util.Objects;

/**
 * One case a statement of a decision tells apart inside itself.
 *
 * <p>A rule is told apart by how each of its conditions came out, and a condition is a whole
 * statement. Two statements draw distinctions a rule does not, and a case is one side of one of
 * them for one statement: a step of the recursion a search from a node took, or a way round the
 * order of one repeated key decides a statement. Measuring the rows and looking for a row are
 * about the same thing, so both name it here.
 */
public sealed interface CaseOfAStatement {

    /** The statement the case is of. */
    Proposition statement();

    /**
     * The steps of a search from a node, which are the steps of the recursion it is and not depths.
     */
    enum Step {
        /** The node meets what the search asks, and the search stops there. */
        AT_THE_NODE,
        /** The node does not, and the search finds one below it. */
        BELOW_IT,
        /** The node does not and has nothing below, where the recursion stops empty. */
        NOWHERE_AT_A_LEAF,
        /** The node does not and every child searched came back empty. */
        NOWHERE_BELOW
    }

    /** The two ways round the order of a repeated key decides a statement. */
    enum Way {
        /** The statement holds with the last element of the key the entry and fails with an
         *  earlier one. */
        HOLDS_BY_THE_LAST,
        /** The statement fails with the last element of the key the entry and holds with an
         *  earlier one. */
        FAILS_BY_THE_LAST
    }

    /** A step of a search the statement states. */
    record Search(Proposition.SomeReachable statement, Step step) implements CaseOfAStatement {

        public Search {
            Objects.requireNonNull(statement, "a step is of some search");
            Objects.requireNonNull(step, "a case is one of the steps");
        }
    }

    /** One way round one order of a repeated key decides the statement. */
    record KeyOrder(Proposition statement, StandingAtAPoint.OrderOfAKey order, Way way)
            implements CaseOfAStatement {

        public KeyOrder {
            Objects.requireNonNull(statement, "an order is read in some statement");
            Objects.requireNonNull(order, "a case is of one order");
            Objects.requireNonNull(way, "a case is one way round");
        }
    }
}
