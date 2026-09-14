package souther.compiler.partition;

import souther.compiler.observe.Incompleteness;

import java.util.Set;

/**
 * Why a generation did not offer everything it might have.
 *
 * <p>Apart from {@code Incompleteness}, which says what a measurement could not read. These say what
 * the generator did about that, and the two are not the same taxonomy: a value that could not be read
 * is a fact about the rows, and a position left out of the offer is a decision taken because of it.
 * Held as one vocabulary, the decision borrowed the name of the cause and a reader could not tell a
 * generation that ended from one that went on without a position.
 *
 * <p>That difference is the whole of what a reader of a generated block needs and could not get. A
 * block that says it stopped, above rows it is offering, is telling an author both that there is work
 * here and that there is none.
 */
public sealed interface GenerationReason {

    /**
     * A position no work was offered at, because some row's value there could not be read.
     *
     * <p>The generation went on without it. A row written for a class at a position nothing is known
     * about may be a row that is already there, and telling an author to write one is worse than
     * saying nothing: it is a specific piece of work that is already done.
     */
    record PositionWithheld(AxisId axis) implements GenerationReason {}

    /**
     * No value was composed anywhere, because the build asked for none.
     *
     * <p>A row offered at a boundary is a value that went through the module's decoders, and
     * composing one costs a decoder run per point — which is work a build that asked to read what
     * its rows already established did not ask for. What the report says about those points is
     * unchanged; what is missing is the row a person could paste.
     */
    record NoValuesWereAskedFor(String behavior) implements GenerationReason {}


    /**
     * Rows exist that nothing read, so nothing was offered at all.
     *
     * <p>What is left uncovered cannot be worked out from rows that were not read, and a generated
     * row is a specific piece of work handed to a person — one that may already be sitting in the
     * file that could not be evaluated.
     *
     * <p>Carries what the measurement could not read, because that is the evidence this decision
     * rests on and a person holding only the generated block has nowhere else to find it. The
     * decision and the evidence are different things and this keeps them so.
     */
    record RowsNotRead(String behavior, Set<Incompleteness.Met> because)
            implements GenerationReason {

        public RowsNotRead {
            because = Set.copyOf(because);
        }
    }

    /**
     * The search ended before it had walked the whole plan, with this many things left on it.
     *
     * <p>Classes and arms, which is what a plan is made of. A combination is where a witness for an
     * arm is looked for and is not a thing the plan holds, so a count of them was a number about a
     * space nobody is owed anything in — and the number handed here was never that anyway.
     */
    record SearchLimit(String behavior, int owed) implements GenerationReason {}

    /**
     * Groups of the body's decisions this did not offer any combination of, because each was wider
     * than the walk offers.
     *
     * <p>Beside {@link SearchLimit} rather than folded into it. That one is a budget that ran out
     * part way through a plan and is lifted by allowing more rows; this is a group nothing walked
     * at all, and no number of rows reaches it. A reader acting on the first would raise a limit
     * that changes nothing here.
     *
     * <p>And only the ones an arm was left waiting on. What a run owes is the classes and the arms
     * a caller names; walking a group is how a row for an arm is looked for, not something anybody
     * is owed. So a group claiming nothing this run was asked for cost it nothing — and neither did
     * one whose arms another group reached, or whose arms the row budget stopped at first, since
     * those arms have an entry of their own saying what happened to them.
     *
     * @param groups how many were held back with an arm still waiting on them at the end, which is
     *               the group's own count and not a count of the combinations in them — the whole
     *               of what this says is that the walk was never made, so how many cells it would
     *               have had is not something anything counted
     */
    record GroupsNotOffered(String behavior, int groups) implements GenerationReason {}

    /**
     * The module's classes were not there to put a candidate through.
     *
     * <p>Which is not the classes refusing to link — that is {@link LinkageFailed}, and it is what
     * happened where they were built and could not be reached. Neither leaves a row to offer, and
     * that is the only thing they have in common; a sentence saying the classes were not there,
     * printed where they were, states something that did not happen.
     */
    record NothingToBuildAgainst(String behavior) implements GenerationReason {}

    /**
     * Rows were offered for combinations of the body's decisions that nothing ran to confirm.
     *
     * <p>Which is not that they are wrong. A row is composed by narrowing each position to the
     * classes the combination leaves it, and whether such a row reaches the meeting is settled by
     * running it; where nothing could, what the row is offered for is what the reading says.
     *
     * <p>Said because silence about it reads as confirmation. The rows are worth offering either
     * way — this is the account a generation could always give of them — but an author acting on
     * one is acting on a reading, and that is theirs to know.
     */
    record RowsNotConfirmed(String behavior) implements GenerationReason {}

    /**
     * The generated classes would not link, so the decoders could not be reached.
     *
     * <p>What the JVM raised is a {@code LinkageError}, and which of its causes it was is not
     * something this can tell. What it does say is that there were classes: the difference from
     * {@link NothingToBuildAgainst} is recorded where the attempt was made, and losing it here would
     * be this compiler choosing which of two things it saw to report.
     */
    record LinkageFailed(String behavior) implements GenerationReason {}
}
