package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.AStopShown;
import souther.compiler.query.About;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.math.BigInteger;
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

    /**
     * A quotient a run works out before an operation, whose divisor is no form of the input's
     * numbers, is one a value is not shown to get past: here every run stops at it, and none gets
     * to {@code q + 1}, so no stop there is shown. Its stop is left untold, which no operation
     * after it is shown past, and a value looked for is asked to get past it as well.
     */
    @Test
    void anOperationAfterAQuotientNotReadIsNotShownToStop() {
        List<AStopShown> shown = shownIn(
                "if Rational.toInt(UP, e / (if p > 0 then 0 else 0)) >= q + 1 then 1 else 2");

        assertEquals(List.of(), shown.stream().filter(each -> each.operation().equals("q + 1"))
                .toList(), shown::toString);
    }

    /**
     * What is shown is that a run stops in an operation as written, at a value, and not at which
     * of the places writing it a run stops first: two places working out {@code p + 1} take a
     * value past its ends both, so a run with it stops in {@code p + 1} at the first, which is
     * what is said.
     */
    @Test
    void aStopShownInAnOperationWrittenAtTwoPlacesIsOneARunWithTheValueStopsIn() {
        List<AStopShown> shown = shownIn("if (p + 1) + (p + 1) > q then 1 else 2");

        assertEquals(List.of(BigInteger.valueOf(Long.MAX_VALUE)), shown.stream()
                .filter(each -> each.operation().equals("p + 1"))
                .flatMap(each -> each.at().stream())
                .filter(each -> each.place().toString().equals("p"))
                .map(AStopShown.NumberAt::number).distinct().toList(), shown::toString);
    }

    /**
     * A quotient stops a run at its own step, past its operands: an operation of its dividend is
     * worked out before it divides, so a run stops in {@code p + 1} at the greatest {@code p},
     * though the divisor is nought there and a run that got past would divide by it.
     */
    @Test
    void anOperationOfADividendStopsARunBeforeTheQuotientDoes() {
        List<AStopShown> shown = shownIn("if Rational.toInt(UP, (p + 1) / (p - 9223372036854775807))"
                + " >= 2 then 1 else 2");

        assertEquals(List.of(BigInteger.valueOf(Long.MAX_VALUE)), shown.stream()
                .filter(each -> each.operation().equals("p + 1"))
                .flatMap(each -> each.at().stream())
                .filter(each -> each.place().toString().equals("p"))
                .map(AStopShown.NumberAt::number).toList(), shown::toString);
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
