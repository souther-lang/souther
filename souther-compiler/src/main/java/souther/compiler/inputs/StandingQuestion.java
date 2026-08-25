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
 * @param rule  which rule of the model raised it, which is what tells one question from another
 * @param cited how a reader finds that rule, which is not what tells it from another
 * @param asks  what it asks and what it asks it about, together
 */
public record StandingQuestion(RuleRef rule, RuleCitation cited, InputQuestion asks) {

    public StandingQuestion {
        if (rule == null || cited == null || asks == null) {
            throw new IllegalArgumentException("a standing question names a rule and what it asks");
        }
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
