package souther.compiler.partition;

import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Proposition;

import java.util.List;
import java.util.Objects;
import java.util.Optional;
import java.util.function.UnaryOperator;

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
     * What tells the case from every other, written whole: the statement by its key, and which
     * case of it. A key within a document, and no sentence.
     */
    String spelled();

    /**
     * Whether a row can be looked for by what the case says of the node a search starts at and of
     * the places inside it that the case names.
     *
     * <p>The criterion for work: a case none of the searches that compose rows can look for is a
     * case the measure still reports as unmeasured, and is no work a person is offered rows for.
     */
    boolean canBeLookedFor();

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

        @Override
        public String spelled() {
            return step + " of " + statement.key();
        }

        @Override
        public boolean canBeLookedFor() {
            return askedOfTheNode(UnaryOperator.identity()).isPresent();
        }

        /**
         * What the step says of the node the search starts at, as statements about that node, or
         * none where a row cannot be asked for the step by what it writes at the node.
         *
         * <p>Finding one below is asked as the start not meeting what the search asks and a node
         * some levels down doing so ({@link #askedAtLevel}); the first level here.
         *
         * @param denying what holds exactly where a statement does not, which is the reading's own
         */
        public Optional<List<Proposition>> askedOfTheNode(UnaryOperator<Proposition> denying) {
            return askedAtLevel(1, denying);
        }

        /**
         * What the step says of the node the search starts at, with finding one below asked of the
         * node {@code levels} down ({@link Proposition.SomeReachable#someNodeBelowMeetingIt});
         * none where the search is not of that form, because a row then has nothing that steers
         * it to a node below. The other three steps are asked the same at every level.
         *
         * <p>Finding one below is a node at some depth, which no one statement says. Each level is
         * a candidate for it, and the rules of the decision may leave room at one and none at
         * another; which levels are tried is the search's ({@link CaseCandidates}).
         */
        public Optional<List<Proposition>> askedAtLevel(int levels,
                                                        UnaryOperator<Proposition> denying) {
            if (!statement.at().equals(statement.writtenAt())) {
                return Optional.empty();
            }
            Proposition notAtTheNode = denying.apply(statement.atANode());
            return switch (step) {
                case AT_THE_NODE -> Optional.of(List.of(statement.atANode()));
                case BELOW_IT -> statement.someNodeBelowMeetingIt(levels)
                        .map(below -> List.of(notAtTheNode, below.meets()));
                case NOWHERE_AT_A_LEAF -> statement.noneBelow()
                        .map(none -> List.of(notAtTheNode, none));
                // What every node below comes to is no statement about the start node: a row is in
                // the case where its run says so, and the walk that composes it goes on to its next
                // assignment while it does not.
                case NOWHERE_BELOW -> statement.noneBelow()
                        .map(none -> List.of(notAtTheNode, denying.apply(none)));
            };
        }

        /** The places the step is asked at {@code levels} below the start, which are the ones a
         *  reading has to have read to say what a row has to be there. None for a step that asks
         *  nothing inside the nodes below. */
        public List<TermPath> placesAtLevel(int levels) {
            return step != Step.BELOW_IT ? List.of()
                    : statement.someNodeBelowMeetingIt(levels)
                            .map(Proposition.SomeReachable.NodeBelowMeeting::places)
                            .orElse(List.of());
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

        @Override
        public String spelled() {
            return way + " of " + order.position() + " in " + order.container() + " in "
                    + statement.key();
        }

        /** Which element of a key held twice is the entry is no statement about one node, and no
         *  search composes a list that holds a key twice toward it. */
        @Override
        public boolean canBeLookedFor() {
            return false;
        }
    }
}
