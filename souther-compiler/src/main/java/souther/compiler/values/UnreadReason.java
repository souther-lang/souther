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
     * A rule stated as an alternative to the ones about this position went unread.
     *
     * <p>The position is left open by a branch that never named it. {@code left /= right || code
     * == "A"} says nothing about {@code code} where the first alternative holds, so the values the
     * second names are not the whole of what {@code code} may be — and what went unread is the
     * other branch rather than anything written about this position.
     *
     * <p>Its own arm because the reason a branch stopped is not a reason about the positions the
     * other branch spoke of. Lent across, {@link #RELATES_TWO_POSITIONS} arrived at a position no
     * comparison had related to anything, and the word it projects to told the author their rule
     * compares it with another.
     */
    ALTERNATIVE_NOT_READ,

    /**
     * A rule about this position is written more deeply nested than this compiler reads.
     *
     * <p>Not a form it has no word for: every part of it is one this reads, and what stopped is how
     * far in the reading goes. Not the machine being too large either — it never got as far as
     * making one. Its own arm because what an author does about it is write the same pattern with
     * fewer brackets, which neither of the others would tell them.
     */
    PATTERN_TOO_DEEPLY_NESTED,

    /**
     * One rule about this position names a set of strings, and making the machine for it is more
     * than this compiler will do.
     *
     * <p>About that rule and naming it. A pattern is a machine as big as it is written, so a rule
     * this refuses is one somebody wrote and could write differently — which is what an author can
     * act on, and what tells this from the reason below.
     */
    PATTERN_TOO_COSTLY,

    /**
     * The rules about this position were read, and the values they leave are more than this
     * compiler will build.
     *
     * <p>Not a form it has no word for, and not one of the rules being too large either. Every rule
     * that reached here was understood and every one of them was turned into the set it names; what
     * ran out was the allowance for what those sets come to between them. Two patterns each small
     * on its own have a meet the size of their product, so this is a fact about the answer and
     * about none of the rules — naming one would tell an author to change a rule that is not why.
     *
     * <p>Widens like the rest. What is left at the position is every value, which is true and is
     * short of what the rules say.
     */
    EXACT_VALUES_TOO_COSTLY,

    /**
     * The reading never reached the rules about this position.
     *
     * <p>Marked as being about neither: there is no rule in hand for it to be about, and it is not
     * a fact about what the rules leave either.
     *
     * <p>A different thing from a rule it read and could not use. The walk that gathers clauses
     * stopped at a type it had already been through, a clause could not be typed and so never
     * arrived, a reading was told not to open the position, a rule of it was not asked for, nothing
     * read the declaration at all, or the reading fell over. Which of those it was is not recorded:
     * none of them is a fact about the rule, and all of them leave the same hole.
     *
     * <p><b>And none of them is a figure this compiler stopped at</b>, which is what tells this
     * from {@link #NOT_REACHED_PAST_DEPTH_LIMIT} and is the whole of why the two are apart. A
     * reading that met one of these meets it again however much a run is allowed.
     *
     * <p>Not every way a walk can stop. One of them hands the rules to a reading one position down,
     * where a row meets them, and the position above admits what it admits (#1072). Which stops
     * those are is settled in one place and not restated here — see {@code PathEngine.leftBy} in
     * {@code souther.compiler.check}, which this package may not name.
     */
    NOT_REACHED,

    /**
     * The reading did not reach the rules about this position, and what stopped it was how far
     * down it could afford to read.
     *
     * <p>The same hole as {@link #NOT_REACHED} and not the same news. What stopped here is a figure
     * this compiler compared a depth against, so a run allowed to read further need not stop at
     * this position at all; every other way of never reaching a position is met again whatever a
     * run allows. Held as one reason, nothing downstream could tell a reader which of the two they
     * were looking at, and a person was as good as told to measure the same thing twice.
     *
     * <p>Said only where the depth is the whole of it. A position some other stop also reaches is
     * one that stays short after the depth is raised, so it is {@link #NOT_REACHED} — the reason
     * is about what a wider reading would leave, and not about which stop happened to be first.
     *
     * <p>About neither a rule nor what the rules leave, like the one above: there is no rule in
     * hand for it to be about. What a document calls it is also the same word, since which figure
     * stopped a walk is this compiler's business and not a promise to a reader.
     */
    NOT_REACHED_PAST_DEPTH_LIMIT;

    /**
     * What a reason is a fact about, which decides who may be shown it.
     *
     * <p>Held by the reason and not by whoever is reading one. The same question was answered in
     * three places — a store deciding what it may file under a rule, a report deciding what to name,
     * a reading deciding which bag to put it in — and three answers to one question is three chances
     * to disagree. Asked here, a reason added arrives with the question already put to whoever added
     * it.
     *
     * <p>Not context-dependent, and if a reason is ever found to be one of these here and the other
     * there, that is two reasons and they are told apart by being two.
     */
    public enum About {

        /**
         * A rule somebody wrote, which a report may name and an author may change.
         *
         * <p>A form nothing reads, a rule relating two positions, a pattern larger than any machine
         * this holds: each of those is about a thing in front of somebody.
         */
        A_RULE,

        /**
         * What the rules leave between them, which names no rule.
         *
         * <p>Every rule that reached the position was read and every one of them was turned into
         * the set it names; what ran out was the allowance for what those come to. The same rules
         * in another order would have been built, so naming the one that happened to be last sends
         * an author to change something that is not why.
         */
        THE_ANSWER,

        /** Neither, because no rule reached the position for anything to be about. */
        NEITHER
    }

    /** What this reason is a fact about — see {@link About}. */
    public About about() {
        return switch (this) {
            case RELATES_TWO_POSITIONS, FORM_NOT_READ, ALTERNATIVE_NOT_READ,
                 PATTERN_TOO_DEEPLY_NESTED, PATTERN_TOO_COSTLY -> About.A_RULE;
            case EXACT_VALUES_TOO_COSTLY -> About.THE_ANSWER;
            case NOT_REACHED, NOT_REACHED_PAST_DEPTH_LIMIT -> About.NEITHER;
        };
    }
}
