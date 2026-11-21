package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.math.BigInteger;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a run may stop in a comparison it stops at the first place that does, so a stop at a
 * place is shown by a value of the input that gets past what the comparison works out before it
 * and asks nothing of what it works out after it. The way to the comparison puts {@code q} at the
 * greatest {@code Int}, so {@code q + 1} stops every run that gets to it, and a stop at the
 * division by {@code p} is shown only if a run does not get that far.
 */
class AStopIsJudgedWithoutWhatARunWorksOutAfterItTest {

    private static final String GREATEST = "9223372036854775807";

    private static String model(String way, String comparison) {
        return """
                module demo

                data Out = Int

                behavior b : (e: Int, p: Int, q: Int) -> Out
                let b (e, p, q) = Out { value =
                    if %s then (if %s then 1 else 2) else 3 }
                """.formatted(way, comparison);
    }

    /** Judged on the way where {@code q} is the greatest {@code Int}. */
    private static List<StopAssessment.Judgement> judged(String comparison) {
        return judgedOn("q >= " + GREATEST, comparison);
    }

    private static List<StopAssessment.Judgement> judgedOn(String way, String comparison) {
        Compilation compilation = ACompiledModel.measured(model(way, comparison),
                new Adequacy.Asked(Adequacy.Level.OFF, false));
        return SitesJudged.of(compilation, "b");
    }

    private static List<StopAssessment.Judgement.Stops> stopsAtADivision(
            List<StopAssessment.Judgement> judged) {
        return judged.stream()
                .filter(StopAssessment.Judgement.Stops.class::isInstance)
                .map(StopAssessment.Judgement.Stops.class::cast)
                .filter(each -> each.shown().site() instanceof StopAssessment.Site.ByNought)
                .toList();
    }

    /** The number {@code shown} holds at the place of the input named {@code place}. */
    private static BigInteger heldAt(StopAssessment.Shown shown, String place) {
        return shown.at().entrySet().stream()
                .filter(each -> each.getKey() instanceof NumericTerm.ValueOf(var path)
                        && path.toString().endsWith(place))
                .map(each -> each.getValue().floor().orNull())
                .findFirst().orElseThrow();
    }

    /**
     * In {@code (e / p) / (q + 1)} the division by {@code p} is worked out before {@code q + 1},
     * so a run that stops at it has not got to {@code q + 1}: the stop is shown at {@code p} of
     * nought, where {@code q + 1} is past its end for the only {@code q} the way allows. The
     * division by {@code q + 1} is worked out after it, and that is not shown.
     */
    @Test
    void aStopAtADivisionIsShownWhereAnOperationAfterItWouldStopEveryRun() {
        List<StopAssessment.Judgement> judged =
                judged("Rational.toInt(DOWN, (e / p) / (q + 1)) >= 2");
        List<StopAssessment.Judgement.Stops> stops = stopsAtADivision(judged);
        assertEquals(1, stops.size(), judged::toString);
        assertEquals(BigInteger.ZERO, heldAt(stops.getFirst().shown(), "p"));
    }

    /**
     * In {@code (e / p) / q}, with nothing on the way, a run stops at the first division where
     * {@code p} is nought whatever {@code q} is, and at the second where {@code q} is nought and
     * {@code p} is not: the second is not asked to hold where the first is judged, and the first
     * is asked to hold where the second is.
     */
    @Test
    void aQuotientOfAQuotientIsToldWholeAndBothDivisionsAreJudged() {
        List<StopAssessment.Judgement> judged =
                judgedOn("e >= 0", "Rational.toInt(DOWN, (e / p) / q) >= 2");
        List<StopAssessment.Judgement.Stops> stops = stopsAtADivision(judged);
        assertEquals(2, stops.size(), judged::toString);
        assertEquals(BigInteger.ZERO, heldAt(stops.get(0).shown(), "p"));
        assertEquals(BigInteger.ZERO, heldAt(stops.get(1).shown(), "q"));
        assertTrue(!heldAt(stops.get(1).shown(), "p").equals(BigInteger.ZERO),
                judged::toString);
    }

    /**
     * {@code q + 1} is worked out before the division by it, so a run that gets to the division
     * has got past {@code q + 1}, which the way keeps it from: no value of the input is shown to
     * stop at the division.
     */
    @Test
    void aStopAtADivisionIsNotShownWhereAnOperationBeforeItStopsEveryRun() {
        List<StopAssessment.Judgement> judged = judged("Rational.toInt(DOWN, e / (q + 1)) >= 2");
        assertEquals(List.of(), stopsAtADivision(judged), judged::toString);
    }
}
