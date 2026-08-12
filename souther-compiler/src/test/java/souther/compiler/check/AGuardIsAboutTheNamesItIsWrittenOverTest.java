package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.check.InvariantChecker.Said;
import souther.compiler.check.InvariantChecker.Verdict;
import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A guard states what it states of the names it is written over, and not only of the values those
 * names were given.
 *
 * <p>A name given a computed value is read through to the arithmetic behind it, so a guard over two
 * such names lands over the fields their bodies read. A field taken off one of those names is keyed
 * as the name, so the construction that takes the difference asks about the names themselves. Both
 * readings are of the same two values and nothing relates them — a name's own atom carries the
 * bounds of the form it was given and not the form — so a guard the author wrote about the very
 * values being built settled nothing, and the same two expressions written out where they stand
 * settled it (#676).
 *
 * <p>Every route below is held to two answers: the difference the guard bounds is proved, and one
 * step past that difference is not. A route silent on both is a route the check never read, which is
 * the silence this file would otherwise be satisfied by, so the verdicts are what these assert.
 */
class AGuardIsAboutTheNamesItIsWrittenOverTest {

    /**
     * Two totals over a monthly remuneration, and the net taken off them. {@code Net} is built only
     * at the site under test, so what is asserted of it is not what a helper's own arithmetic
     * answered.
     */
    private static final String MODEL = """
            module demo

            data Yen = Decimal
                invariant value >= 0.0m

            data Net = Decimal
                invariant value >= 0.0m

            data Rem = { base: Yen, commute: Yen }
            data TooMuch

            let grossOf (r: Rem, uplift: Yen): Yen = r.base + uplift
            let takenOf (r: Rem, si: Yen): Yen = r.commute + si

            behavior boundFirst : (r: Rem, uplift: Yen, si: Yen) -> Net | TooMuch
                constructs Net, TooMuch

            """;

    /** How the check came out on each construction of {@code source}. */
    private static List<Said> verdictsIn(String source) {
        List<Said> said = Collections.synchronizedList(new ArrayList<>());
        InvariantChecker.WATCHING = said;
        try {
            Compiler.compileWithWarnings(source);
        } finally {
            InvariantChecker.WATCHING = null;
        }
        assertFalse(said.isEmpty(), "nothing was checked, so nothing here is being held to anything");
        return said;
    }

    /** The verdict on every {@code Net} the body builds, which is at least one: a type nothing was
     * said of is a construction the check never reached. */
    private static void reads(Verdict expected, String body) {
        String source = MODEL + body;
        List<Verdict> on = verdictsIn(source).stream()
                .filter(s -> s.type().equals("Net")).map(Said::verdict).toList();
        assertFalse(on.isEmpty(), "no construction of `Net` was checked at all:\n" + body);
        for (Verdict verdict : on) {
            assertEquals(expected, verdict, "on the `Net` built by:\n" + body);
        }
    }

    private static boolean warns(String body) {
        return Compiler.compileWithWarnings(MODEL + body).warnings().stream()
                .anyMatch(d -> d.severity() == Severity.WARNING && "E2011".equals(d.code()));
    }

    /**
     * One route, held to the boundary its guard draws. The difference the guard bounds is proved,
     * and the same difference less one is an unknown the author is told about — which is what says
     * the route was read at all, rather than passed over.
     */
    private static void bounds(String settled, String past) {
        reads(Verdict.PROVED, settled);
        assertFalse(warns(settled), "nothing is reported of a construction the guard settled");
        reads(Verdict.UNKNOWN, past);
        assertTrue(warns(past), "and an author is told where it reaches no further");
    }

    // --- the parameters themselves --------------------------------------------------------------

    @Test
    void parametersComparedAsTheNewtypesTheyAre() {
        bounds("""
                let boundFirst (r, uplift, si) = {
                    guard uplift >= si else TooMuch
                    Net(uplift.value - si.value)
                }
                """, """
                let boundFirst (r, uplift, si) = {
                    guard uplift >= si else TooMuch
                    Net(uplift.value - si.value - 1.0m)
                }
                """);
    }

    @Test
    void parametersComparedOnTheirValues() {
        bounds("""
                let boundFirst (r, uplift, si) = {
                    guard uplift.value >= si.value else TooMuch
                    Net(uplift.value - si.value)
                }
                """, """
                let boundFirst (r, uplift, si) = {
                    guard uplift.value >= si.value else TooMuch
                    Net(uplift.value - si.value - 1.0m)
                }
                """);
    }

    // --- a name given a parameter ---------------------------------------------------------------

    @Test
    void namesGivenAParameterComparedAsTheNewtypesTheyAre() {
        bounds("""
                let boundFirst (r, uplift, si) = {
                    let gross = uplift
                    let taken = si
                    guard gross >= taken else TooMuch
                    Net(gross.value - taken.value)
                }
                """, """
                let boundFirst (r, uplift, si) = {
                    let gross = uplift
                    let taken = si
                    guard gross >= taken else TooMuch
                    Net(gross.value - taken.value - 1.0m)
                }
                """);
    }

    @Test
    void namesGivenAParameterComparedOnTheirValues() {
        bounds("""
                let boundFirst (r, uplift, si) = {
                    let gross = uplift
                    let taken = si
                    guard gross.value >= taken.value else TooMuch
                    Net(gross.value - taken.value)
                }
                """, """
                let boundFirst (r, uplift, si) = {
                    let gross = uplift
                    let taken = si
                    guard gross.value >= taken.value else TooMuch
                    Net(gross.value - taken.value - 1.0m)
                }
                """);
    }

    // --- the two totals written out where they stand ---------------------------------------------

    @Test
    void callsWrittenOutTwiceComparedAsTheNewtypesTheyAre() {
        bounds("""
                let boundFirst (r, uplift, si) = {
                    guard grossOf(r, uplift) >= takenOf(r, si) else TooMuch
                    Net(grossOf(r, uplift).value - takenOf(r, si).value)
                }
                """, """
                let boundFirst (r, uplift, si) = {
                    guard grossOf(r, uplift) >= takenOf(r, si) else TooMuch
                    Net(grossOf(r, uplift).value - takenOf(r, si).value - 1.0m)
                }
                """);
    }

    @Test
    void callsWrittenOutTwiceComparedOnTheirValues() {
        bounds("""
                let boundFirst (r, uplift, si) = {
                    guard grossOf(r, uplift).value >= takenOf(r, si).value else TooMuch
                    Net(grossOf(r, uplift).value - takenOf(r, si).value)
                }
                """, """
                let boundFirst (r, uplift, si) = {
                    guard grossOf(r, uplift).value >= takenOf(r, si).value else TooMuch
                    Net(grossOf(r, uplift).value - takenOf(r, si).value - 1.0m)
                }
                """);
    }

    // --- a name given a computed value, which is what #676 is about ------------------------------

    /** The shape the issue was written from: each total is used twice, so each is given a name. */
    @Test
    void namesGivenACallComparedAsTheNewtypesTheyAre() {
        bounds("""
                let boundFirst (r, uplift, si) = {
                    let gross = grossOf(r, uplift)
                    let taken = takenOf(r, si)
                    guard gross >= taken else TooMuch
                    Net(gross.value - taken.value)
                }
                """, """
                let boundFirst (r, uplift, si) = {
                    let gross = grossOf(r, uplift)
                    let taken = takenOf(r, si)
                    guard gross >= taken else TooMuch
                    Net(gross.value - taken.value - 1.0m)
                }
                """);
    }

    @Test
    void namesGivenACallComparedOnTheirValues() {
        bounds("""
                let boundFirst (r, uplift, si) = {
                    let gross = grossOf(r, uplift)
                    let taken = takenOf(r, si)
                    guard gross.value >= taken.value else TooMuch
                    Net(gross.value - taken.value)
                }
                """, """
                let boundFirst (r, uplift, si) = {
                    let gross = grossOf(r, uplift)
                    let taken = takenOf(r, si)
                    guard gross.value >= taken.value else TooMuch
                    Net(gross.value - taken.value - 1.0m)
                }
                """);
    }

    /** The same with the arithmetic the helpers do written where the name is given: a call is not
     * what the check reads through, the value being computed is. */
    @Test
    void namesGivenTheArithmeticThoseCallsDo() {
        bounds("""
                let boundFirst (r, uplift, si) = {
                    let gross = r.base + uplift
                    let taken = r.commute + si
                    guard gross >= taken else TooMuch
                    Net(gross.value - taken.value)
                }
                """, """
                let boundFirst (r, uplift, si) = {
                    let gross = r.base + uplift
                    let taken = r.commute + si
                    guard gross >= taken else TooMuch
                    Net(gross.value - taken.value - 1.0m)
                }
                """);
    }

    /** One side a name given a computed value and the other a parameter: the comparison is stated
     * over the name on the side that has one, and over what it was given on the side that does. */
    @Test
    void oneNameGivenACallAndOneParameter() {
        bounds("""
                let boundFirst (r, uplift, si) = {
                    let gross = grossOf(r, uplift)
                    guard gross >= si else TooMuch
                    Net(gross.value - si.value)
                }
                """, """
                let boundFirst (r, uplift, si) = {
                    let gross = grossOf(r, uplift)
                    guard gross >= si else TooMuch
                    Net(gross.value - si.value - 1.0m)
                }
                """);
    }

    // --- the guard written one way and the construction the other -------------------------------

    /**
     * The two sides written the other way round from the guard, one at a time. Putting an
     * initializer back where its name stands changes nothing about what is built, so a guard over
     * the names reaches it — a reading that held only where both sides were spelled as the guard
     * spelled them would be the same defect one step over, on a body an author is as likely to
     * write.
     */
    @Test
    void theGuardOverNamesAndTheConstructionOverOneInitializer() {
        bounds("""
                let boundFirst (r, uplift, si) = {
                    let gross = grossOf(r, uplift)
                    let taken = takenOf(r, si)
                    guard gross >= taken else TooMuch
                    Net(gross.value - takenOf(r, si).value)
                }
                """, """
                let boundFirst (r, uplift, si) = {
                    let gross = grossOf(r, uplift)
                    let taken = takenOf(r, si)
                    guard gross >= taken else TooMuch
                    Net(gross.value - takenOf(r, si).value - 1.0m)
                }
                """);
    }

    @Test
    void theGuardOverNamesAndTheConstructionOverTheOtherInitializer() {
        bounds("""
                let boundFirst (r, uplift, si) = {
                    let gross = grossOf(r, uplift)
                    let taken = takenOf(r, si)
                    guard gross >= taken else TooMuch
                    Net(grossOf(r, uplift).value - taken.value)
                }
                """, """
                let boundFirst (r, uplift, si) = {
                    let gross = grossOf(r, uplift)
                    let taken = takenOf(r, si)
                    guard gross >= taken else TooMuch
                    Net(grossOf(r, uplift).value - taken.value - 1.0m)
                }
                """);
    }

    /** And the guard itself written over one name and one initializer. */
    @Test
    void theGuardOverOneNameAndOneInitializer() {
        bounds("""
                let boundFirst (r, uplift, si) = {
                    let gross = grossOf(r, uplift)
                    let taken = takenOf(r, si)
                    guard gross >= takenOf(r, si) else TooMuch
                    Net(gross.value - taken.value)
                }
                """, """
                let boundFirst (r, uplift, si) = {
                    let gross = grossOf(r, uplift)
                    let taken = takenOf(r, si)
                    guard gross >= takenOf(r, si) else TooMuch
                    Net(gross.value - taken.value - 1.0m)
                }
                """);
    }

    // --- a name standing inside the comparison ---------------------------------------------------

    /** A name inside an operand rather than being one: what the comparison is about is arithmetic
     * over the name, and the construction takes the same arithmetic. */
    @Test
    void aNameStandingInsideTheComparison() {
        bounds("""
                let boundFirst (r, uplift, si) = {
                    let gross = grossOf(r, uplift)
                    let taken = takenOf(r, si)
                    guard gross + si >= taken else TooMuch
                    Net(gross.value + si.value - taken.value)
                }
                """, """
                let boundFirst (r, uplift, si) = {
                    let gross = grossOf(r, uplift)
                    let taken = takenOf(r, si)
                    guard gross + si >= taken else TooMuch
                    Net(gross.value + si.value - taken.value - 1.0m)
                }
                """);
    }

    /** And the same where the arithmetic is on the side the guard bounds from below. */
    @Test
    void aNameStandingInsideTheOtherOperand() {
        bounds("""
                let boundFirst (r, uplift, si) = {
                    let gross = grossOf(r, uplift)
                    let taken = takenOf(r, si)
                    guard gross >= taken + si else TooMuch
                    Net(gross.value - taken.value - si.value)
                }
                """, """
                let boundFirst (r, uplift, si) = {
                    let gross = grossOf(r, uplift)
                    let taken = takenOf(r, si)
                    guard gross >= taken + si else TooMuch
                    Net(gross.value - taken.value - si.value - 1.0m)
                }
                """);
    }

    /** And a guard states an order and not an equality: what is on the other side of the one the
     * author wrote is no more settled for having been named. */
    @Test
    void theOrderAGuardStatesIsTheOneItStates() {
        reads(Verdict.UNKNOWN, """
                let boundFirst (r, uplift, si) = {
                    let gross = grossOf(r, uplift)
                    let taken = takenOf(r, si)
                    guard gross >= taken else TooMuch
                    Net(taken.value - gross.value)
                }
                """);
    }
}
