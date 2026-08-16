package souther.compiler.values;

/**
 * Why a reading could not say which values a position holds.
 *
 * <p>What is recorded is what this reading could not do, at the coarseness the reading itself can
 * tell apart. It is not what a document says: a report writes its own word for one of these, and
 * two of them may well be one word out there. Kept as this compiler's own vocabulary so that a
 * capability gained here removes a case here without moving anything a document promises.
 *
 * <p>Every arm widens. A position carrying one of these admits the values the reading arrived at
 * and may admit fewer — never more — so a reader deciding that a value is impossible may use the
 * set whichever arm is beside it, and a reader deciding that the set is the whole of what the model
 * says may not.
 */
public enum UnreadReason {

    /**
     * The rule relates this position to another rather than saying which values it holds.
     *
     * <p>{@code a /= b} says where one position stands against another, and what is held here is a
     * set of one position's values. Nothing about the rule was beyond this reading — both sides
     * were recognised — so this is not a form it failed on.
     */
    RELATES_TWO_POSITIONS,

    /**
     * A rule naming this position is written in a form this reading does not take apart as a set of
     * values: a call, a pattern, a comparison against something other than a written value.
     */
    FORM_NOT_READ,

    /**
     * The reading never reached the rules about this position.
     *
     * <p>A different thing from a rule it read and could not use. The walk that gathers clauses
     * stopped — at a depth, at a type it had already been through, at one with no declaration to
     * read — or a clause could not be typed and so never arrived. Which of those it was is not
     * recorded: none of them is a fact about the rule, and all of them leave the same hole.
     */
    NOT_REACHED
}
