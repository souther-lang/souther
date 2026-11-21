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
 *
 * <p>Each case is a behavior of the one module, which is compiled once for all of them.
 */
class AStopIsJudgedWithoutWhatARunWorksOutAfterItTest {

    private static final String GREATEST = "9223372036854775807";

    /** A comparison, and the way the program takes to it. */
    private record Case(String way, String comparison) {

        /** On the way where {@code q} is the greatest {@code Int}. */
        Case(String comparison) {
            this("q >= " + GREATEST, comparison);
        }
    }

    private static final Case DIVISION_AFTER = new Case(
            "Rational.toInt(DOWN, (e / p) / (q + 1)) >= 2");
    private static final Case DIVISION_OF_DIVISION = new Case("e >= 0",
            "Rational.toInt(DOWN, (e / p) / q) >= 2");
    private static final Case DIVISION_BY_SUM = new Case("Rational.toInt(DOWN, e / (q + 1)) >= 2");
    private static final Case LET_BODY_AFTER = new Case("(q + 1) + { let t = e\n q + 2 } >= 2");
    private static final Case LET_BODY_BEFORE = new Case("{ let t = e\n q + 2 } + (q + 1) >= 2");
    private static final Case FUNCTION_BODY = new Case(
            "q >= " + GREATEST + " && p >= " + GREATEST,
            "List.fold((w, l) -> q + 1, p + 1, [1]) >= 2");

    private static final List<Case> CASES = List.of(DIVISION_AFTER, DIVISION_OF_DIVISION,
            DIVISION_BY_SUM, LET_BODY_AFTER, LET_BODY_BEFORE, FUNCTION_BODY);

    /** The module of every case, compiled when the first is judged. */
    private static final class Module {

        static final Compilation COMPILED = compile();

        private static Compilation compile() {
            StringBuilder model = new StringBuilder("module demo\n\ndata Out = Int\n");
            for (int each = 0; each < CASES.size(); each++) {
                model.append("""

                        behavior b%1$d : (e: Int, p: Int, q: Int) -> Out
                        let b%1$d (e, p, q) = Out { value =
                            if %2$s then (if %3$s then 1 else 2) else 3 }
                        """.formatted(each, CASES.get(each).way(), CASES.get(each).comparison()));
            }
            return ACompiledModel.measured(model.toString(),
                    new Adequacy.Asked(Adequacy.Level.OFF, false));
        }
    }

    private static List<StopAssessment.Judgement> judged(Case each) {
        return SitesJudged.of(Module.COMPILED, "b" + CASES.indexOf(each));
    }

    private static List<StopAssessment.Judgement.Stops> stopsAtADivision(
            List<StopAssessment.Judgement> judged) {
        return judged.stream()
                .filter(StopAssessment.Judgement.Stops.class::isInstance)
                .map(StopAssessment.Judgement.Stops.class::cast)
                .filter(each -> each.shown().site() instanceof StopAssessment.Site.ByNought)
                .toList();
    }

    /** The stops shown at the operation written {@code written}. */
    private static List<StopAssessment.Judgement.Stops> stopsAt(
            List<StopAssessment.Judgement> judged, String written) {
        return judged.stream()
                .filter(StopAssessment.Judgement.Stops.class::isInstance)
                .map(StopAssessment.Judgement.Stops.class::cast)
                .filter(each -> each.shown().site().written().equals(written))
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
        List<StopAssessment.Judgement> judged = judged(DIVISION_AFTER);
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
        List<StopAssessment.Judgement> judged = judged(DIVISION_OF_DIVISION);
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
        List<StopAssessment.Judgement> judged = judged(DIVISION_BY_SUM);
        assertEquals(List.of(), stopsAtADivision(judged), judged::toString);
    }

    /**
     * The body of a {@code let} is worked out whenever the {@code let} is, but it is no step of it
     * ({@code Evaluated.inOrder} lists the value), so {@code q + 2} has no place: it is worked out
     * after {@code q + 1} all the same, and a run that stops at {@code q + 1} has not got to it.
     */
    @Test
    void aStopIsShownWhereAnOperationInALetBodyAfterItWouldStopEveryRun() {
        List<StopAssessment.Judgement> judged = judged(LET_BODY_AFTER);
        List<StopAssessment.Judgement.Stops> stops = stopsAt(judged, "q + 1");
        assertEquals(1, stops.size(), judged::toString);
        assertEquals(new BigInteger(GREATEST), heldAt(stops.getFirst().shown(), "q"));
    }

    /**
     * The control: the body of the {@code let} is worked out before {@code q + 1}, so a run that
     * gets to {@code q + 1} has got past {@code q + 2}, which the way keeps it from: no value of
     * the input is shown to stop at {@code q + 1}.
     */
    @Test
    void aStopIsNotShownWhereAnOperationInALetBodyBeforeItWouldStopEveryRun() {
        List<StopAssessment.Judgement> judged = judged(LET_BODY_BEFORE);
        assertEquals(List.of(), stopsAt(judged, "q + 1"), judged::toString);
    }

    /**
     * The body of a function value runs when it is applied, and {@code List.fold} applies it after
     * its arguments are worked out, so a run that stops at {@code q + 1} in the body has got past
     * {@code p + 1}, which the way keeps it from: no value is shown to stop at {@code q + 1}.
     */
    @Test
    void aStopInAFunctionValueIsNotShownWhereAnArgumentOfTheCallStopsEveryRun() {
        List<StopAssessment.Judgement> judged = judged(FUNCTION_BODY);
        assertEquals(List.of(), stopsAt(judged, "q + 1"), judged::toString);
    }
}
