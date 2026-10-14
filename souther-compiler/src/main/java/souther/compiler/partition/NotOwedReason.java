package souther.compiler.partition;

/**
 * Why a border owes no row in one of its four roles.
 *
 * <p>A statement about the model or about the values, and never a report of a search that came back
 * empty. Each of these used to be a coverage item that was not built — the obligation was left out of
 * a list, and every one of them arrived downstream as the same thing, one fewer entry. What a reader
 * has to do about them is opposite: a point no value can stand at has been discharged and is counted
 * out, and a point no carrier names is one the technique asks for and this language cannot write
 * down. Left to a count, both read as the report being short.
 *
 * <p>Two and not more, because there are two things that settle it: whether any value stands at the
 * point, and what the carrier can name. Both can hold of one border at once — an invariant on a
 * {@code Decimal} refuses the far side and names no neighbour either — and the one said is the one
 * about the model, since a reader told that this language has no name for a value that may not exist
 * would go looking for a missing conversion.
 *
 * <p>What kind of rule drew the line settles which points a border <em>has</em> and never whether a
 * row is owed at one it has ({@link Border#pointsOf}). A rule that names a value has a point
 * outside it on each side, so there is nothing for it to decline; a bound has the same points as
 * any other order and no value stands at the ones outside it, which is the first of these.
 */
public enum NotOwedReason {

    /**
     * No value can stand where the point is, so there is nowhere to write it.
     *
     * <p>What an invariant's bound says about both the points outside it: nothing beyond the bound
     * can be constructed, so there is no row to write and no class over there to cover. The same
     * sentence covers a side one value wide — {@code guard x <= 0} under {@code invariant x >= 0} has
     * its own {@code ON} point at zero and nothing inside away from it. And it covers a point no rule
     * is written about: a {@code Set<Bool>} holds each of two values once, so a count of it past two
     * is a point nothing stands at.
     *
     * <p>The conclusion and not what proved it. A type with few values, a rule on the type, a rule on
     * a container's size and how many of an element's values meet a statement each prove it, two of
     * them can prove one point alike, and what a reader does about the point is the same whichever
     * did. The point is excluded, the word the specification uses for what is counted out of what
     * the rows are held to.
     */
    NO_VALUE_CAN_STAND_THERE,

    /**
     * The border is drawn and the order the quantity is on names no value the point could be at.
     *
     * <p>Two ways that happens and one answer. A {@code Decimal} and a {@code String} have no next
     * value, at a place or at the difference two terms of a line between them stand at — the two
     * carriers this language names no step for, a date-time and a time of day each stepping at the
     * unit they are held to. And a form over positions whose values fill takes some of the numbers
     * and not all of them: {@code 3 * a} comes arbitrarily close to one and never arrives, because
     * no decimal a model writes is a third.
     *
     * <p>The point the technique asks for cannot be written down either way, which is a limit of the
     * language and not a gap in the rows: an item that cannot exist is not one anybody is short of.
     */
    THE_CARRIER_NAMES_NO_NEIGHBOUR
}
