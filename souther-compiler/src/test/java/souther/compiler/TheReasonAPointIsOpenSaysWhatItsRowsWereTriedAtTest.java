package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A point of a comparison a run works out, which no candidate row reaches, says what the
 * candidates were — in the report a reader is given, read whole.
 *
 * <p>The sentence is read after "writes some of" and before "rather than all of them", so a test
 * that holds the sentence on its own does not hold how it reads there. The figures and the
 * wording are written out here and not asked of the code that writes them, since moving either is
 * a decision about what the search tries and what the reader is told.
 */
class TheReasonAPointIsOpenSaysWhatItsRowsWereTriedAtTest {

    private static final String BESIDE = " rows beside those with an element put in a list or"
            + " changed for one a row of the module ran or a whole number moved by one";

    private static final String SIZES = "the containers the comparison names each holding the"
            + " same number of elements from 0 to 6 with element values left to their types and"
            + " then" + BESIDE;

    private static final String VALUES = "the whole numbers it names outside a container all at"
            + " one of {0, 1, -1, 2} and then" + BESIDE;

    private static final String NO_ROW_AT_ON = "nothing could show a row can be written at the ON"
            + " point";

    /**
     * The same, with points that are even only. A total of an odd number below the first the score
     * resets to is one no row comes to, whatever the search writes, and nothing in the types shows
     * it — so a point there stays open however far the search goes.
     */
    private static String evenModel(String reached, String signature, String row) {
        return model("0 && Int.floorMod(value, 2) == 0", reached, signature, row);
    }

    /** The model of a fold over a list of points, whose comparison is the one under test. */
    private static String model(String lowest, String reached, String signature, String row) {
        return """
                module m

                data Points = Int
                    invariant value >= %s && value <= 12

                data Score = Int
                    invariant value >= 0 && value <= 50

                behavior add : (s: Score, p: Points) -> Score

                let add (s, p) = {
                    let t = s.value + p.value
                    if t > 50 then Score(25) else Score(t)
                }

                example add
                    | (Score(48), Points(4)) -> Score(25)
                    | (Score(48), Points(2)) -> Score(50)
                    | (Score(0), Points(2)) -> Score(2)
                    | (Score(40), Points(12)) -> Score(25)
                    | (Score(38), Points(12)) -> Score(50)
                    | (Score(25), Points(10)) -> Score(35)
                    | (Score(50), Points(2)) -> Score(25)

                behavior total : (ps: List<Points>) -> Score

                let total (ps) = List.fold((s, p) -> add(s, p), Score(0), ps)

                example total
                    | ([]) -> Score(0)

                behavior reached : %s -> Bool

                let reached %s

                example reached
                    | %s -> false
                """.formatted(lowest, signature, reached, row);
    }

    private static String report(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String told(String candidates) {
        return "writes some of the rows whose run works out a number at the item (written with "
                + candidates + ") rather than all of them";
    }

    /** A comparison that names a list is told its sizes and nothing of whole numbers. */
    @Test
    void aComparisonNamingOnlyAListIsToldItsSizes() {
        String human = report(evenModel("(ps) = total(ps).value == 21", "(ps: List<Points>)",
                "([])"));
        assertTrue(human.contains(NO_ROW_AT_ON), human);
        assertTrue(human.contains(told(SIZES)), human);
        assertFalse(human.contains("whole numbers it names"), human);
        assertFalse(human.contains("other than a row"), human);
    }

    /** A comparison that names a whole number outside a container is told its values. */
    @Test
    void aComparisonNamingOnlyAWholeNumberIsToldItsValues() {
        String human = report(evenModel("(q) = total([q, q]).value == 21", "(q: Points)",
                "(Points(2))"));
        assertTrue(human.contains(told(VALUES)), human);
        assertFalse(human.contains("number of elements"), human);
    }

    /** A comparison that names both is told both, as one population. */
    @Test
    void aComparisonNamingBothIsToldBoth() {
        String human = report(evenModel("(ps, q) = total(ps).value + q.value == 21",
                "(ps: List<Points>, q: Points)", "([], Points(2))"));
        assertTrue(human.contains(told(SIZES + " and " + VALUES)), human);
    }

    /**
     * A comparison that names no container and no whole number has no candidate, so the report does
     * not say that some of a population was written: it says that none was composed.
     */
    @Test
    void aComparisonNamingNoPlaceIsToldNothingWasComposedAndNoPopulation() {
        String human = report(model("0",
                "(b) = total(if b then [Points(1)] else [Points(2)]).value == 20", "(b: Bool)",
                "(true)"));
        assertTrue(human.contains(NO_ROW_AT_ON), human);
        assertTrue(human.contains("nothing composed one"), human);
        assertFalse(human.contains("writes some of the rows whose run"), human);
    }

    /**
     * What the command reference says of reach is what the search does. Where the lowest value of
     * the element is 0 every candidate list sums to 0, so a total of 20 is reached only by a row
     * beside the candidates, with elements unlike one another; a total no list comes to stays
     * open. At a lowest value of 1 a list of the right number of elements sums to the total and
     * the candidates reach it.
     */
    @Test
    void theReachTheCommandReferenceDescribesIsTheReachOfTheSearch() {
        String reachedAt21 = "(ps) = total(ps).value == 21";
        String reachedAt20 = "(ps) = total(ps).value == 20";
        String reachedAt5 = "(ps) = total(ps).value == 5";
        String signature = "(ps: List<Points>)";

        assertTrue(report(evenModel(reachedAt21, signature, "([])")).contains(NO_ROW_AT_ON));
        assertFalse(report(model("0", reachedAt20, signature, "([])")).contains(NO_ROW_AT_ON));
        assertFalse(report(model("0", reachedAt5, signature, "([])")).contains(NO_ROW_AT_ON));
        assertFalse(report(model("1", reachedAt5, signature, "([])")).contains(NO_ROW_AT_ON));
    }
}
