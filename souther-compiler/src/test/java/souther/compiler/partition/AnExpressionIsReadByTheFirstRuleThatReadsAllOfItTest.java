package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Derivation;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhyUnread;
import souther.compiler.semantics.ConditionJoin;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which of the rules that take an expression it is read by ({@link RuleChoice}).
 *
 * <p>Over rules written here, each saying what it met as it went, so what is held is the choice and
 * not what any one rule of the reading happens to do today: a rule that stopped part of the way does
 * not hide one tried after it that read all of it, the parts a rule set aside met are not parts of
 * what is stated, and whether a rule read all of an expression is asked of what it concludes.
 */
class AnExpressionIsReadByTheFirstRuleThatReadsAllOfItTest {

    private static final WhyUnread OWED =
            new WhyUnread.NotYetComposed(WhyUnread.NotYetComposed.Step.A_SIZE_AN_OPERATION_KEEPS);

    private static final Derivation READ = new Derivation.ATruthAtAPosition(TermPath.of("a"), true);

    /** A rule that meets {@code part} and answers {@code with}. */
    private static Supplier<Derivation> meeting(List<String> met, String part, Derivation with) {
        return () -> {
            met.add(part);
            return with;
        };
    }

    /** A rule that takes nothing. */
    private static Derivation takingNothing() {
        return null;
    }

    private static Proposition concluded(Derivation derivation) {
        return derivation.concludes(Optional.empty());
    }

    /**
     * A step owed is an obligation until a rule takes it, and then what is stated is the rule's
     * conclusion, derived by that rule.
     */
    @Test
    void aStepOwedIsReadOnceARuleTakesIt() {
        List<String> met = new ArrayList<>();
        Derivation before = RuleChoice.firstThatReadsIt(
                List.of(meeting(met, "owed", new Derivation.Stopped(OWED, false))), met);
        assertTrue(concluded(before) instanceof Proposition.Unread unread
                && unread.why().equals(OWED), "the part is left unread, owed the step it is owed");

        met.clear();
        Derivation after = RuleChoice.firstThatReadsIt(List.of(
                meeting(met, "owed", new Derivation.Stopped(OWED, false)),
                meeting(met, "read", READ)), met);
        assertSame(READ, after, "the rule that took it is the one it is derived by");
        assertEquals(new Proposition.Truth(new DecisionSubject.AnInput(TermPath.of("a")), true),
                concluded(after));
        assertEquals(List.of("read"), met,
                "what the rule set aside met is no part of what is stated");
    }

    @Test
    void whereNoRuleReadsAllOfItTheFirstThatTookItIsKept() {
        List<String> met = new ArrayList<>(List.of("before"));
        Derivation first = new Derivation.Stopped(OWED, false);
        Derivation chosen = RuleChoice.firstThatReadsIt(List.of(
                AnExpressionIsReadByTheFirstRuleThatReadsAllOfItTest::takingNothing,
                meeting(met, "first", first),
                meeting(met, "second", new Derivation.Stopped(OWED, true))), met);
        assertSame(first, chosen);
        assertEquals(List.of("before", "first"), met,
                "what was met before the choice stays, and only the kept rule's parts join it");
    }

    @Test
    void whereNoRuleTakesItThereIsNothing() {
        List<String> met = new ArrayList<>(List.of("before"));
        assertNull(RuleChoice.firstThatReadsIt(List.of(
                AnExpressionIsReadByTheFirstRuleThatReadsAllOfItTest::takingNothing,
                AnExpressionIsReadByTheFirstRuleThatReadsAllOfItTest::takingNothing), met));
        assertEquals(List.of("before"), met);
    }

    /**
     * A part nothing read beside one that settles the whole is no part of what is stated: whether a
     * rule read all of an expression is asked of what it concludes, not of the steps it took.
     */
    @Test
    void aStopTheConclusionSettlesLeavesNothingUnread() {
        List<String> met = new ArrayList<>();
        Derivation settled = new Derivation.Joined(ConditionJoin.BOTH,
                new Derivation.WrittenOut(false), new Derivation.Stopped(OWED, false));
        Derivation chosen = RuleChoice.firstThatReadsIt(List.of(
                meeting(met, "settled", settled), meeting(met, "read", READ)), met);
        assertSame(settled, chosen, "false beside anything is read in full");
        assertEquals(new Proposition.Always(false), concluded(chosen));
        assertEquals(List.of("settled"), met);
    }

    /** Two rules that read all of an expression state one thing, whichever is tried first. */
    @Test
    void whichOfTwoRulesThatReadItAllIsTriedFirstStatesNothingDifferent() {
        Derivation twiceDenied = new Derivation.UnderADenial(
                new Derivation.UnderADenial(READ, true), true);
        List<String> met = new ArrayList<>();
        Derivation oneWay = RuleChoice.firstThatReadsIt(List.of(
                meeting(met, "denied", twiceDenied), meeting(met, "read", READ)), met);
        Derivation otherWay = RuleChoice.firstThatReadsIt(List.of(
                meeting(met, "read", READ), meeting(met, "denied", twiceDenied)), met);
        assertEquals(concluded(oneWay), concluded(otherWay));
    }
}
