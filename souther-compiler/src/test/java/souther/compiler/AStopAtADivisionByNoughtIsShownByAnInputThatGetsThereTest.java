package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.AStopShown;
import souther.compiler.query.About;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A stop at a division is shown by an input that gets to the division and holds its divisor at
 * nought, and by no other. What is shown is read off the finding itself, the division and the
 * number each place holds, and not off how the report says it.
 */
class AStopAtADivisionByNoughtIsShownByAnInputThatGetsThereTest {

    private static List<AStopShown> shownIn(String expression) {
        Compilation compilation = ACompiledModel.measured("""
                module demo

                data Out = Int

                behavior b : (e: Int, p: Int, q: Int) -> Out
                let b (e, p, q) = Out { value = %s }
                """.formatted(expression), Adequacy.Asked.fullReport());
        List<AStopShown> out = new ArrayList<>();
        for (Adequacy.Finding each : AdequacyReport.of(compilation).findings()) {
            if (each.about() instanceof About.ARuleThatMayStopARun(var finding)) {
                out.addAll(finding.shown());
            }
        }
        return out;
    }

    private static final String QUOTIENT = "Rational.toInt(UP, e / p) >= 2";

    @Test
    void anInputThatHoldsTheDivisorAtNoughtShowsTheStop() {
        List<AStopShown> shown = shownIn("if " + QUOTIENT + " then 1 else 2");
        assertEquals(1, shown.size(), shown::toString);
        assertEquals("division by p", shown.getFirst().operation());
        assertEquals(1, shown.getFirst().at().stream()
                .filter(each -> each.place().toString().equals("p")).count());
        shown.getFirst().at().stream().filter(each -> each.place().toString().equals("p"))
                .forEach(each -> assertEquals(0, each.number().signum()));
    }

    /** A divisor of several numbers is one form of them, and a run stops where it is nought. */
    @Test
    void aDivisorThatIsASumShowsTheStopWhereTheSumIsNought() {
        List<AStopShown> shown = shownIn("if Rational.toInt(UP, e / (p + 1)) >= 2 then 1 else 2");
        AStopShown stop = shown.stream()
                .filter(each -> each.operation().equals("division by p + 1")).findFirst()
                .orElseThrow(() -> new AssertionError(shown.toString()));
        assertEquals(-1, stop.at().stream().filter(each -> each.place().toString().equals("p"))
                .findFirst().orElseThrow().number().intValueExact());
        assertTrue(shownIn("if p >= 0 then (if Rational.toInt(UP, e / (p + 1)) >= 2 then 1"
                + " else 2) else 3").stream()
                .noneMatch(each -> each.operation().startsWith("division")));
    }

    /** The outer quotient is worked out after one whose divisor is no form of the numbers, and a
     *  run that stops in that one does not get to it: no stop is shown at the outer. */
    @Test
    void noStopIsShownPastAQuotientWhoseDivisorIsNotRead() {
        assertTrue(shownIn("if Rational.toInt(UP, (e / (p * q)) / p) >= 2 then 1 else 2").stream()
                .noneMatch(each -> each.operation().equals("division by p")));
    }

    @Test
    void aWayThatKeepsTheDivisorFromNoughtShowsNone() {
        assertEquals(List.of(), shownIn("if p >= 1 then (if " + QUOTIENT + " then 1 else 2)"
                + " else 3"));
    }

    @Test
    void aWayThatHoldsTheDivisorAtNoughtShowsTheStopAtIt() {
        List<AStopShown> shown = shownIn("if p == 0 then (if " + QUOTIENT + " then 1 else 2)"
                + " else 3");
        assertTrue(shown.stream().anyMatch(each -> each.operation().equals("division by p")),
                shown::toString);
    }

    /** The quotient is worked out on an arm no run takes: no run stops there, and none is shown. */
    @Test
    void aQuotientOnAnArmNoRunTakesShowsNone() {
        assertEquals(List.of(), shownIn("if q <= 0 then (if (if q > 0 then Rational.toInt(UP, e / p)"
                + " else 1) >= 2 then 1 else 2) else 3"));
    }
}
