package souther.compiler.partition;

import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhyUnread;

/**
 * Which of the lines one comparison states is this one, as the reading that took the comparison
 * apart named it.
 *
 * <p>A comparison states one rule, and a rule stating several relations held together draws a line
 * for each of them: {@code Int.max(a, b) <= g} is one rule with a line on {@code a} and one on
 * {@code b}. Which of the two a line is is the answer of the reading that found them, and only
 * that reading makes one — so nothing that meets a line afterwards can number the lines of a
 * comparison by a count of its own, and a reader handed one can only have been handed it.
 *
 * <p>The relation the line is, held. A helper's comparison is read once per call, and each call's
 * statement is taken apart on its own; what two calls' lines share is the relation, and where each
 * fell among the relations its own call stated is that call's and nothing the other knows. A name
 * taken from that place makes one relation two lines in two calls and two relations one. Not where
 * the relation was written either: one relation stated twice is one line.
 *
 * <p>Or, where a statement on one application was read as far as a number nothing holds, what it
 * came to there. That reading has no relation to name — the relation is linear and cannot be
 * written down — and it draws no line, so it is told from the others only for being a different
 * part of the comparison.
 */
public final class PartOfAComparison {

    /** The statement held, as a proposition spells it: one spelling for one relation. */
    private final String spelled;

    private PartOfAComparison(String spelled) {
        this.spelled = spelled;
    }

    /** The line {@code relation} draws. */
    public static PartOfAComparison of(Proposition.Compared relation) {
        if (!relation.holds()) {
            throw new IllegalArgumentException("a line is the relation held: " + relation);
        }
        return new PartOfAComparison(relation.key());
    }

    /**
     * The line a statement that is one line draws: the relation it states, whichever way round, or
     * the number nothing holds that it was read as far as.
     */
    static PartOfAComparison ofTheStatement(Proposition stated) {
        return switch (stated) {
            case Proposition.Compared compared ->
                    of(compared.holds() ? compared : (Proposition.Compared) compared.denied());
            case Proposition.Unread unread when unread.why() instanceof WhyUnread.ANumberNotHeld ->
                    new PartOfAComparison((unread.holds() ? unread : unread.denied()).key());
            default -> throw new IllegalArgumentException(
                    "a statement that is one line states a relation: " + stated);
        };
    }

    /** The relation, as the reading spelled it: what tells this line from the comparison's others. */
    public String spelled() {
        return spelled;
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof PartOfAComparison that && spelled.equals(that.spelled);
    }

    @Override
    public int hashCode() {
        return spelled.hashCode();
    }

    @Override
    public String toString() {
        return "line " + spelled;
    }
}
