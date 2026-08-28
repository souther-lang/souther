package souther.compiler.inputs;

import souther.compiler.check.RuleCitation;
import souther.compiler.check.RuleRef;

/**
 * One question a rule of the model raises that nothing answered, as everything past the input
 * boundary carries it.
 *
 * <p>The other side of {@code check.RuleAccounting.Unanswered}, which is the same question in the
 * vocabulary of the declaration whose clauses raised it. What crosses is what a reader out here
 * asks: which rule, how a reader finds it, and what the question is about.
 *
 * <p><b>The question it came from is not carried beside it.</b> Nothing downstream reads anything
 * of it that is not here — the rule, the citation, and what it asks, which is the arm — and holding
 * it would leave a second identity for the same question reachable, so that every comparison
 * downstream had two answers to choose between. That choice is what the crossing exists to take
 * away.
 *
 * @param rule    which rule of the model raised it, which is what tells one question from another
 * @param cited   how a reader finds that rule, which is not what tells it from another
 * @param asks    what it asks and what it asks it about, together
 * @param stopped what this compiler was short of, which is why the question stands. In its own
 *                terms and not a document's, so a reader out here is told what was missing without
 *                a published word reaching back into what a reading may record; which word a
 *                document writes for one of these is {@link ReportedReason}'s.
 *
 *                <p>About the rule and never about the place. The question carries the rule, and
 *                what it is short of is short of that rule — a reason about the position it stands
 *                at answers a different question and belongs to whoever asks that one.
 *
 *                <p>Every one of them, in the order the parts of the clause were met. A question is
 *                answered when every part that asked it has been read, so a part standing behind
 *                another is a second thing to lift — and which of them a reader met would otherwise
 *                turn on the order their author wrote them in.
 *
 *                <p>Never empty. A question that nothing answered was left standing by something,
 *                and an empty list here would say a rule went unaccounted for with nothing to act
 *                on.
 */
public record StandingQuestion(RuleRef rule, RuleCitation cited, InputQuestion asks,
                               java.util.List<BlockReason.AboutARule> stopped) {

    public StandingQuestion {
        if (rule == null || cited == null || asks == null) {
            throw new IllegalArgumentException("a standing question names a rule and what it asks");
        }
        if (stopped == null || stopped.isEmpty()) {
            throw new IllegalArgumentException("a question stands because something was short of it");
        }
        stopped = java.util.List.copyOf(stopped);
    }

    /** What it asks, which follows from what it is about. */
    public souther.compiler.check.CoverageObligation obligation() {
        return asks.obligation();
    }

    @Override
    public String toString() {
        return obligation() + " at " + asks;
    }
}
