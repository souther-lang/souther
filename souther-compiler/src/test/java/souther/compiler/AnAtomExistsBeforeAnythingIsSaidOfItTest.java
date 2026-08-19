package souther.compiler;

import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A value the invariant-discharge check can point at is one it can point at before anything has been
 * said about it.
 *
 * <p>Two questions, and holding them apart is what this is. Whether a value has a name here is
 * decided by what computes it: one expression is one value, so two writings of it are one unknown.
 * Whether anything is known of that value is decided by what the guards state. Deciding the first
 * question by the answer to the second makes them circular — a guard about a value could only be read
 * once something had been read about that value — and the first guard about any value is the one that
 * falls into it.
 *
 * <p>What that cost: a guard naming a value the check has no rule about was spent making the value
 * nameable and its own relation was dropped, so the construction it established was reported; and the
 * same expression written out rather than named was not even asked, so the construction it did not
 * establish was silent. Each is checked here against a construction that must be refused, since a
 * silence that is a proof and a silence that is a value nobody looked at read alike.
 */
class AnAtomExistsBeforeAnythingIsSaidOfItTest {

    private static final String MODULE = """
            module demo

            data NonNeg = Int
                invariant value >= 0
            data Fine

            behavior f : (%s) -> NonNeg | Fine
                constructs NonNeg

            let f (%s) = {
                %s
            }
            """;

    /** How many warnings the check reports of {@code body}, over inputs {@code params}. */
    private static long warnings(String params, String names, String body) {
        return Compiler.compileWithWarnings(MODULE.formatted(params, names, body)).warnings().stream()
                .filter(d -> d.severity() == Severity.WARNING).count();
    }

    private static final String LIST = "xs: List<Int>, bill: Int";

    /**
     * The first guard about a value states what it states.
     *
     * <p>`List.sum` is a call the check has no rule about, so this guard is the first thing in the
     * body to mention the value it answers. What follows from it — that the difference is not
     * negative — follows from the guard alone and from nothing about summing.
     */
    @Test
    void theFirstGuardAboutAValueStatesWhatItStates() {
        assertEquals(0, warnings(LIST, "xs, bill", """
                let t = List.sum(xs)
                    guard t >= bill else Fine
                    NonNeg(t - bill)"""),
                "`t >= bill` is what makes `t - bill` non-negative");
        assertEquals(1, warnings(LIST, "xs, bill", """
                let t = List.sum(xs)
                    guard t >= bill else Fine
                    NonNeg(t - bill - 1)"""),
                "and one more subtraction is not something it establishes");
    }

    /**
     * Guards about one value answer the same in either order, and what they answer is discharged.
     *
     * <p>Both are said rather than only that the two agree. Two orders that both report is agreement
     * as much as two that both discharge, and it is the answer this is about: the second statement
     * is what establishes the construction, so an order in which it goes unread is an order in which
     * the construction is reported.
     */
    @Test
    void guardsAboutOneValueAnswerTheSameInEitherOrder() {
        long spokenFirst = warnings(LIST, "xs, bill", """
                let t = List.sum(xs)
                    guard t >= 0 else Fine
                    guard t >= bill else Fine
                    NonNeg(t - bill)""");
        long spokenSecond = warnings(LIST, "xs, bill", """
                let t = List.sum(xs)
                    guard t >= bill else Fine
                    guard t >= 0 else Fine
                    NonNeg(t - bill)""");
        assertEquals(0, spokenFirst, "`t >= bill` establishes it, stated second");
        assertEquals(0, spokenSecond, "and stated first");
        assertEquals(spokenFirst, spokenSecond, "the same two statements, in the other order");
    }

    /** Written out or named, one call is one value — in both directions, so that neither spelling is
     * the one that goes unasked. */
    @Test
    void aCallAnswersTheSameWrittenOrNamed() {
        assertEquals(warnings(LIST, "xs, bill", """
                guard List.sum(xs) >= bill else Fine
                    NonNeg(List.sum(xs) - bill)"""),
                warnings(LIST, "xs, bill", """
                let t = List.sum(xs)
                    guard t >= bill else Fine
                    NonNeg(t - bill)"""),
                "one value discharged, however it is written");
        assertEquals(warnings(LIST, "xs, bill", """
                guard List.sum(xs) >= bill else Fine
                    NonNeg(List.sum(xs) - bill - 1)"""),
                warnings(LIST, "xs, bill", """
                let t = List.sum(xs)
                    guard t >= bill else Fine
                    NonNeg(t - bill - 1)"""),
                "and one value left standing, however it is written");
    }

    /** A construction from a call no guard mentions is owed its clause. Nothing here says the sum is
     * not negative, and nothing about the operation says it either. */
    @Test
    void aCallNoGuardMentionsIsOwedItsClause() {
        assertEquals(1, Compiler.compileWithWarnings("""
                module demo

                data NonNeg = Int
                    invariant value >= 0

                behavior f : (xs: List<Int>) -> NonNeg
                    constructs NonNeg

                let f (xs) = {
                    let t = List.sum(xs)
                    NonNeg(t)
                }
                """).warnings().stream().filter(d -> d.severity() == Severity.WARNING).count(),
                "the clause is read against the value and nothing discharges it");
    }

    /**
     * Moving the call into a helper answers what the call answers.
     *
     * <p>The rewrite a reader reaches for when the warning arrives. It is expanded where the check
     * reads the body, so it is the same value under another name, and a construction it does not
     * establish is refused through the helper exactly as it is through the call.
     */
    @Test
    void aHelperWrappingTheCallAnswersLikeTheCall() {
        String tally = "\n\nlet tally (xs: List<Int>): Int = List.sum(xs)";
        assertEquals(0, Compiler.compileWithWarnings(MODULE.formatted(LIST, "xs, bill", """
                guard tally(xs) >= bill else Fine
                    NonNeg(tally(xs) - bill)""") + tally).warnings().stream()
                .filter(d -> d.severity() == Severity.WARNING).count(),
                "the guard establishes it through the helper");
        assertEquals(1, Compiler.compileWithWarnings(MODULE.formatted(LIST, "xs, bill", """
                guard tally(xs) >= bill else Fine
                    NonNeg(tally(xs) - bill - 1)""") + tally).warnings().stream()
                .filter(d -> d.severity() == Severity.WARNING).count(),
                "and does not establish one more subtraction");
    }

    private static final String PRODUCT = "a: Int, b: Int, bill: Int";

    /**
     * A product the fragment does not read is still one value.
     *
     * <p>The domain declines to relate {@code a * b} to {@code a} and to {@code b}, which is a
     * decision about arithmetic and not about naming. A guard comparing the product to something is
     * about the product, and both spellings of it are the same product.
     */
    @Test
    void aProductOutsideTheFragmentIsStillOneValue() {
        assertEquals(0, warnings(PRODUCT, "a, b, bill", """
                guard a * b >= bill else Fine
                    NonNeg(a * b - bill)"""),
                "written out");
        assertEquals(0, warnings(PRODUCT, "a, b, bill", """
                let v = a * b
                    guard v >= bill else Fine
                    NonNeg(v - bill)"""),
                "and named");
        assertEquals(1, warnings(PRODUCT, "a, b, bill", """
                guard a * b >= bill else Fine
                    NonNeg(a * b - bill - 1)"""),
                "one more subtraction is not established, written out");
        assertEquals(1, warnings(PRODUCT, "a, b, bill", """
                let v = a * b
                    guard v >= bill else Fine
                    NonNeg(v - bill - 1)"""),
                "nor named");
    }

    /**
     * What the fragment cannot read is the product and not the sum it sits in.
     *
     * <p>Reading the whole of {@code a * b + c} as one value would lose the {@code + c}, and with it
     * everything a guard about {@code c} states. So the two guards compose here, and a construction
     * one unit past what they establish is still refused.
     */
    @Test
    void aProductInsideArithmeticKeepsTheArithmetic() {
        assertEquals(0, warnings("a: Int, b: Int, c: Int", "a, b, c", """
                guard a * b >= 5 else Fine
                    guard c >= 0 else Fine
                    NonNeg(a * b + c - 5)"""),
                "the product is at least five and the rest is not negative");
        assertEquals(1, warnings("a: Int, b: Int, c: Int", "a, b, c", """
                guard a * b >= 5 else Fine
                    guard c >= 0 else Fine
                    NonNeg(a * b + c - 6)"""),
                "and neither guard says the sum reaches six");
    }
}
