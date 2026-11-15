package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A way that keeps a value off numbers nothing else holds it beside takes no value of the run the
 * value has: beside each of its values the others take one that makes the condition hold. So what
 * is compared of the value past such a way is read over every value, as it is past no condition.
 *
 * <p>The numbers are a disequality's other side, or the elements of a container the way asks to
 * hold the value or to hold nothing equal to it. A rule that ties them to the value, or another
 * statement of the way that reads them, takes the claim away.
 */
class AWayThatKeepsAValueOffNumbersNothingElseHoldsLeavesItsRunWholeTest {

    private static final String NOT_SHOWN = "not shown to reach every value";

    private static String report(String declarations, String parameters, String body) {
        Compilation compilation = Compilation.ofSource("""
                module p
                %s
                behavior f : (%s) -> Bool
                let f = %s
                """.formatted(declarations, parameters, body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** Whether the report says of {@code place} that what it is related to is not shown to reach
     *  every value of it. */
    private static boolean notShownAt(String human, String place) {
        return human.lines().anyMatch(line -> line.contains(NOT_SHOWN)
                && line.contains("about `" + place + "`"));
    }

    /** Past the membership of {@code d} the other side still reaches every {@code s}: the set
     *  holds {@code d} or holds nothing equal to it, whatever {@code d} is. */
    @Test
    void aValueChosenByAMembershipIsComparedOverEveryValue() {
        String human = report("", "hs: Set<Decimal>, d: Decimal, s: Decimal",
                "(hs, d, s) -> (if Set.contains(d, hs) then d + 1.0m else d) >= s");

        assertFalse(human.contains(NOT_SHOWN), human);
    }

    /** The second membership is asked past the first failing, which keeps every element off
     *  {@code d}: the line {@code d + 1 == element} is one that statement never takes a row off,
     *  so {@code d} and the element are each left over every value. */
    @Test
    void aMembershipAskedPastAnotherFailingIsReadOverEveryValue() {
        String human = report("", "hs: Set<Decimal>, d: Decimal",
                "(hs, d) -> Set.contains(d, hs) || Set.contains(d + 1.0m, hs)");

        assertFalse(notShownAt(human, "d"), human);
        assertFalse(notShownAt(human, "hs[*]"), human);
    }

    /** One value is kept off another that nothing else reads, so every value of the first has a
     *  partner that differs. */
    @Test
    void aValueKeptOffAFreeNumberIsComparedOverEveryValue() {
        String human = report("", "h: Decimal, d: Decimal, s: Decimal",
                "(h, d, s) -> (if d /= h then d else 5.0m) >= s");

        assertFalse(notShownAt(human, "d"), human);
        assertFalse(notShownAt(human, "s"), human);
    }

    /** The same two numbers in one record, with nothing between them. */
    @Test
    void aRecordsTwoFieldsNothingTiesAreAsFreeAsTwoParameters() {
        String human = report("data P = { d: Decimal, h: Decimal }", "p: P, s: Decimal",
                "(p, s) -> (if p.d /= p.h then p.d else 5.0m) >= s");

        assertFalse(notShownAt(human, "p.d"), human);
        assertFalse(notShownAt(human, "s"), human);
    }

    /** A rule of the declarations that ties the fields is one the claim does not answer
     *  for: a value kept off a number the rule holds beside it is shown nothing of. */
    @Test
    void aRuleTyingTheNumbersTakesTheClaimAway() {
        String human = report("data P = { d: Decimal, h: Decimal } invariant d <= h",
                "p: P, s: Decimal",
                "(p, s) -> (if p.d /= p.h then p.d else 5.0m) >= s");

        assertTrue(notShownAt(human, "p.d") || notShownAt(human, "s"), human);
    }

    /** A number kept off a constant takes no value that equals it, and the constant is no number
     *  of a row to differ from. */
    @Test
    void aValueKeptOffAConstantIsNotClaimedWhole() {
        String human = report("", "h: Decimal, d: Decimal, s: Decimal",
                "(h, d, s) -> (if d /= 1.0m then d else 5.0m) >= s");

        assertTrue(notShownAt(human, "s"), human);
    }
}
