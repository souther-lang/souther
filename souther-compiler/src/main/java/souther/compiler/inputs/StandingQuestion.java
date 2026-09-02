package souther.compiler.inputs;

import souther.compiler.check.RuleCitation;
import souther.compiler.check.RuleRef;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

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
public record StandingQuestion(Fact fact, Set<RuleCitation> cited,
                               List<BlockReason.AboutARule> stopped) {

    public StandingQuestion {
        if (fact == null) {
            throw new IllegalArgumentException("a standing question names a rule and what it asks");
        }
        cited = cited == null ? Set.of() : Set.copyOf(cited);
        if (cited.isEmpty()) {
            throw new IllegalArgumentException("a question names a rule a reader can be sent to");
        }
        if (stopped == null || stopped.isEmpty()) {
            throw new IllegalArgumentException("a question stands because something was short of it");
        }
        stopped = List.copyOf(stopped);
    }

    /** One reader's account of it, as that reader produced it. */
    public static StandingQuestion of(RuleRef rule, RuleCitation cited, InputQuestion asks,
                                      List<BlockReason.AboutARule> stopped) {
        return new StandingQuestion(new Fact(rule, asks), Set.of(cited), stopped);
    }

    /** Which rule raised it. */
    public RuleRef rule() {
        return fact.rule();
    }

    /** What it asks and what it asks it about. */
    public InputQuestion asks() {
        return fact.asks();
    }

    /**
     * Both readers' accounts, as one: the question, with every handle either offered.
     *
     * <p>What each was short of is not accumulated and not chosen between. It is the author's
     * order over the parts of the rule that raised the question, which is one answer about the
     * model — so two accounts of one question that disagree about it are two accounts one of which
     * is wrong, and taking either would publish a precedence nothing in the model decides.
     */
    public StandingQuestion mergedWith(StandingQuestion other) {
        if (!fact.equals(other.fact)) {
            throw new IllegalArgumentException("two accounts put together are of one question: "
                    + fact + " and " + other.fact);
        }
        if (!stopped.equals(other.stopped)) {
            throw new IllegalArgumentException("two accounts of one question disagree about what"
                    + " the author wrote it short of: " + stopped + " and " + other.stopped);
        }
        Set<RuleCitation> both = new HashSet<>(cited);
        both.addAll(other.cited);
        return new StandingQuestion(fact, both, stopped);
    }

    /**
     * What makes two of these one question: which rule raised it, and what it asks.
     *
     * <p>Both of the others are left out, and each says so where it is declared. The citation is
     * how a reader finds the rule and not what tells it from another. What the question is short of
     * is why it stands rather than which question it is.
     */
    public record Fact(RuleRef rule, InputQuestion asks) {

        public Fact {
            if (rule == null || asks == null) {
                throw new IllegalArgumentException("a standing question names a rule and what it"
                        + " asks");
            }
        }
    }

    /** What it asks, which follows from what it is about. */
    public souther.compiler.check.CoverageObligation obligation() {
        return asks().obligation();
    }

    @Override
    public String toString() {
        return obligation() + " at " + asks();
    }
}
