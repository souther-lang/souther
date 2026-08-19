package souther.compiler.partition;

/**
 * Why a border owes no row in one of its four roles.
 *
 * <p>A statement about the model or about the values, and never a report of a search that came back
 * empty. Each of these used to be a coverage item that was not built — the obligation was left out of
 * a list, and every one of them arrived downstream as the same thing, one fewer entry. What a reader
 * has to do about them is opposite: a point the rules refuse has been discharged and is counted out,
 * and a point no carrier names is one the technique asks for and this language cannot write down.
 * Left to a count, both read as the report being short.
 *
 * <p>Three and not more, because there are three things that settle it: what the rules leave, what
 * the carrier can name, and what kind of rule drew the line. Two of these can hold of one border at
 * once — an invariant on a {@code Decimal} refuses the far side and names no neighbour either — and
 * the one said is the one about the model, since a reader told that this language has no name for a
 * value that may not exist would go looking for a missing conversion.
 */
public enum NotOwedReason {

    /**
     * The rules leave no value for the point to be written at.
     *
     * <p>What an invariant's bound says about both the points outside it: nothing beyond the bound
     * can be constructed, so there is no row to write and no class over there to cover. The same
     * sentence covers a side the rules leave one value wide — {@code guard x <= 0} under
     * {@code invariant x >= 0} has its own {@code ON} point at zero and nothing inside away from it —
     * because that is the rules refusing every other value, one arity up. The point is excluded,
     * which is the word the specification already uses for a case the model's own rules refuse.
     */
    THE_RULES_REFUSE_IT,

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
    THE_CARRIER_NAMES_NO_NEIGHBOUR,

    /**
     * The rule names a value rather than ordering the values around it.
     *
     * <p>What an equality draws. {@code x == 5} says which value is singled out and says nothing
     * about which side of it anything is on, so there is no side for a nearest-outside point to be
     * nearest on — 4 and 6 stand alike, and choosing one would invent the answer. What such a rule
     * does divide is the value from every other value, which the {@code OUT} point covers.
     */
    THE_RULE_NAMES_A_VALUE_NOT_A_SIDE
}
