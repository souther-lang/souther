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
     * The border is drawn and the carrier names no value one step from it.
     *
     * <p>A {@code Decimal}, a {@code DateTime} and a {@code String} have no next value. The point
     * the technique asks for cannot be written down in this language, which is a limit of the
     * language and not a gap in the rows: an item that cannot exist is not one anybody is short of.
     */
    THE_CARRIER_NAMES_NO_NEIGHBOUR,

    /**
     * The point one step from a line between two positions, which this reading has no way to name.
     *
     * <p>Told apart from the carrier having no next value, which is what it used to be said as, and
     * that was false of every whole number: the pair one step inside {@code a < b} is the pair where
     * {@code a} is {@code b} less one, and an {@code Int} names both of those values perfectly well.
     * What is missing is a criterion — every one this reading has is about a place at a term, and
     * the step here is on the difference the two terms fall apart by, which is at neither of them.
     *
     * <p>So it is a fact about this compiler, said in the words this report keeps for those, and not
     * about the model or about the values. What would close it is a criterion over the relation
     * rather than over a place; nothing needs one yet, and a reason that blamed the carrier would
     * have the next reader looking for a conversion that is already there.
     */
    THIS_READING_NAMES_NO_POINT_BESIDE_A_RELATION,

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
