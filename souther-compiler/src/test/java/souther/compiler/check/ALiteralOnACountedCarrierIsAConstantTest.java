package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.check.InvariantChecker.Said;
import souther.compiler.check.InvariantChecker.Verdict;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A value written out on a carrier that counts is a constant of this arithmetic.
 *
 * <p>Not a rule about dates. What a written value counts as is the carrier's one answer, and the
 * arithmetic reads whatever it answers with — so a carrier added is read here without a line being
 * written for it.
 *
 * <p><b>Substitution is what this measures.</b> A checker whose proof power falls when a variable is
 * replaced by a concrete value is one whose answers depend on how a model is spelled, which is the
 * property every other reading here is held to. So each carrier is asked the same three things: what
 * it proves, what it refutes, and that a proposition proved over names survives its values being
 * written in.
 *
 * <p>And a carrier that counts nothing stays out. A string is ordered and its values stand no
 * measurable distance apart, so nothing about it is a constant of an affine form — which is the
 * carrier's own answer and not a case this file writes.
 */
class ALiteralOnACountedCarrierIsAConstantTest {

    /** A relation between two positions on a counted carrier, stated by the declaration. */
    private static final String DATES = """
            module demo.dates
            data Period = { from: Date, to: Date }
                invariant Date.daysBetween(from, to) >= 0
            """;

    /** The same shape over the carrier that has always counted, as the control. */
    private static final String NUMBERS = """
            module demo.numbers
            data Span = { lo: Int, hi: Int }
                invariant lo <= hi
            """;

    /** The control: a number written out discharges the rule it satisfies. */
    @Test
    void aNumberWrittenOutIsAConstant() {
        reads(Verdict.PROVED, NUMBERS + """
                behavior mk : (n: Int) -> Span constructs Span
                let mk (n) = Span { lo = 3, hi = 5 }
                """);
    }

    /** And a date written out is one on its own carrier, which is the same rule. */
    @Test
    void aDateWrittenOutIsAConstant() {
        reads(Verdict.PROVED, DATES + """
                behavior mk : (n: Int) -> Period constructs Period
                let mk (n) = Period { from = Date("2026-08-03"), to = Date("2026-08-05") }
                """);
    }

    /** Both carriers refute what their written values refute, so neither is proved by being unread. */
    @Test
    void aNumberWrittenOutRefutesWhatItRefutes() {
        reads(Verdict.REFUTED_ALONE, NUMBERS + """
                behavior mk : (n: Int) -> Span constructs Span
                let mk (n) = Span { lo = 5, hi = 3 }
                """);
    }

    /** The same of a date, which is what says the reading is of the values and not of the shape. */
    @Test
    void aDateWrittenOutRefutesWhatItRefutes() {
        reads(Verdict.REFUTED_ALONE, DATES + """
                behavior mk : (n: Int) -> Period constructs Period
                let mk (n) = Period { from = Date("2026-08-05"), to = Date("2026-08-03") }
                """);
    }

    /**
     * Substituting concrete values into a proposition this proves does not take the proof away.
     *
     * <p>The pair of the two above, and the whole point of them. The guard states the relation over
     * names and the construction states it over values, and a reading that took one and not the
     * other would be answering about the spelling.
     */
    @Test
    void whatIsProvedOverNamesIsProvedOverTheValuesTheyStandFor() {
        reads(Verdict.PROVED, DATES + """
                data Reversed
                behavior mk : (a: Date, b: Date) -> Period | Reversed constructs Period
                let mk (a, b) =
                    if Date.daysBetween(a, b) >= 0 then Period { from = a, to = b }
                    else Reversed
                """);
    }

    /**
     * A carrier that counts nothing is left where it was, and a rule ordering its values still
     * reaches the answers it always reached.
     *
     * <p>The negative control, and it is an invariance rather than an absence. A string is ordered
     * and its values stand no measurable distance apart, so a reading that made a constant of every
     * literal there is would put one into an arithmetic with no number for it — which the language
     * refuses outright rather than answering wrongly. A control asserting some verdict of its own
     * would pass whichever way that guard went; these answers are the ones the refusal comes out of,
     * so a reading that took the guard away stops here.
     */
    @Test
    void anOrderingOverStringsIsReadTheWayItAlwaysWas() {
        reads(Verdict.PROVED, TEXT + """
                behavior mk : (n: Int) -> Tag constructs Tag
                let mk (n) = Tag("abd")
                """);
        reads(Verdict.UNKNOWN, TEXT + """
                behavior mk : (s: String) -> Tag constructs Tag
                let mk (s) = Tag(s)
                """);
    }

    /** An order with no counts under it, for the control above. */
    private static final String TEXT = """
            module demo.text
            data Tag = String
                invariant value >= "abc"
            """;

    /** The verdicts this check reached, and that it reached one: a construction nothing judged
     *  would otherwise read as a construction nothing is owed on. */
    private static void reads(Verdict expected, String source) {
        List<Said> said = Collections.synchronizedList(new ArrayList<>());
        InvariantChecker.WATCHING = said;
        try {
            Compiler.compileWithWarnings(source);
        } catch (souther.compiler.diag.CompileException refused) {
            if (!expected.refuted()) {
                throw refused;
            }
        } finally {
            InvariantChecker.WATCHING = null;
        }
        List<Verdict> reached = said.stream().map(Said::verdict).toList();
        assertFalse(reached.isEmpty(), "no construction was judged at all");
        assertEquals(List.of(expected), reached);
    }
}
