package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What each ordered type is measured at, written out rather than left to be inferred.
 *
 * <p>Which values a line can be drawn on used to be decided in several places, and they disagreed:
 * a {@code Date} was a carrier to the reader that drew a {@code guard}'s line and not to the one
 * that read an invariant's bound, so the same rule about the same position answered two ways
 * depending on where it was written. A table of the answers is what makes that visible — a
 * disagreement is two cells of one row differing, which nothing shorter than this shows.
 *
 * <p>Three numbers per cell and not one. How many positions the model divides, how many lines the
 * rules drew, and what the reading could not read are three separate answers, and a cell that got
 * the first right and the third wrong is what {@code not derivable} on a bounded position was.
 *
 * <p><b>Every carrier appears in both rows.</b> A rule written as an invariant and the same rule
 * written as a {@code guard} reach the measure through different readers, so a row missing from one
 * of them is a reader nothing holds to the other. The bare and the wrapped forms are both here for
 * the same reason: a newtype is the value it carries (spec §primitives), and a cell where the two
 * differ is a name changing what a rule means.
 */
class OneCarrierTableAnswersForEveryOrderedTypeTest {

    /**
     * One cell.
     *
     * @param axes        positions the model divides into classes
     * @param obligations lines some rule drew that a row is owed at
     * @param unread      what stopped a rule being read, or null where nothing did
     */
    private record Measured(int axes, int obligations, String unread) {}

    /** A carrier read all the way through: an axis, the line and the value beside it where the
     *  values step, and nothing left unread. */
    private static Measured read(int obligations) {
        return new Measured(1, obligations, null);
    }

    /** A carrier there is no count to embed into. The rule is named and not drawn. */
    private static final Measured NO_CARRIER =
            new Measured(0, 0, "it is compared against values no line can be drawn on here");

    /** The same, at a position whose type states classes of its own — which a cut does not add to. */
    private static final Measured NO_CARRIER_BUT_CLASSED =
            new Measured(1, 0, "it is compared against values no line can be drawn on here");

    private static final String MODEL = """
            module example.matrix

            data Ok
            data No
            data Verdict = Ok | No

            data Prospecting
            data Qualified
            data Won
            data Stage = Prospecting | Qualified | Won

            data WholeN  = Int
            data DenseN  = Decimal
            data DayN    = Date
            data MomentN = DateTime
            data TextN   = String
            data StageN  = Stage

            data WholeI  = Int      invariant value >= 100
            data DenseI  = Decimal  invariant value >= 0.5m
            data DayI    = Date     invariant value >= Date("2026-01-01")
            data MomentI = DateTime invariant value >= DateTime("2026-01-01T00:00:00")
            data TextI   = String   invariant value >= "2020-01"
            data StageI  = Stage    invariant value >= Qualified

            behavior guardWholeBare : (x: Int) -> Verdict
                constructs Ok, No
            let guardWholeBare (x) = { guard x < 5000 else Ok
                No }

            behavior guardDenseBare : (x: Decimal) -> Verdict
                constructs Ok, No
            let guardDenseBare (x) = { guard x < 0.5m else Ok
                No }

            behavior guardDayBare : (x: Date) -> Verdict
                constructs Ok, No
            let guardDayBare (x) = { guard x < Date("2026-08-01") else Ok
                No }

            behavior guardMomentBare : (x: DateTime) -> Verdict
                constructs Ok, No
            let guardMomentBare (x) = { guard x < DateTime("2026-08-01T00:00:00") else Ok
                No }

            behavior guardTextBare : (x: String) -> Verdict
                constructs Ok, No
            let guardTextBare (x) = { guard x < "2026-08" else Ok
                No }

            behavior guardStageBare : (x: Stage) -> Verdict
                constructs Ok, No, Qualified
            let guardStageBare (x) = { guard x < Qualified else Ok
                No }

            behavior guardWholeWrapped : (x: WholeN) -> Verdict
                constructs Ok, No
            let guardWholeWrapped (x) = { guard x.value < 5000 else Ok
                No }

            behavior guardDenseWrapped : (x: DenseN) -> Verdict
                constructs Ok, No
            let guardDenseWrapped (x) = { guard x.value < 0.5m else Ok
                No }

            behavior guardDayWrapped : (x: DayN) -> Verdict
                constructs Ok, No
            let guardDayWrapped (x) = { guard x.value < Date("2026-08-01") else Ok
                No }

            behavior guardMomentWrapped : (x: MomentN) -> Verdict
                constructs Ok, No
            let guardMomentWrapped (x) = {
                guard x.value < DateTime("2026-08-01T00:00:00") else Ok
                No }

            behavior guardTextWrapped : (x: TextN) -> Verdict
                constructs Ok, No
            let guardTextWrapped (x) = { guard x.value < "2026-08" else Ok
                No }

            behavior guardStageWrapped : (x: StageN) -> Verdict
                constructs Ok, No, Qualified
            let guardStageWrapped (x) = { guard x.value < Qualified else Ok
                No }

            behavior boundWhole  : (x: WholeI)  -> Ok
                constructs Ok
            let boundWhole (x) = Ok

            behavior boundDense  : (x: DenseI)  -> Ok
                constructs Ok
            let boundDense (x) = Ok

            behavior boundDay    : (x: DayI)    -> Ok
                constructs Ok
            let boundDay (x) = Ok

            behavior boundMoment : (x: MomentI) -> Ok
                constructs Ok
            let boundMoment (x) = Ok

            behavior boundText   : (x: TextI)   -> Ok
                constructs Ok
            let boundText (x) = Ok

            behavior boundStage  : (x: StageI)  -> Ok
                constructs Ok
            let boundStage (x) = Ok

            behavior twoLinesDense : (x: Decimal) -> Verdict
                constructs Ok, No
            let twoLinesDense (x) = { guard x < 1.0m else Ok
                guard x < 2.0m else No
                Ok }

            behavior twoLinesMoment : (x: DateTime) -> Verdict
                constructs Ok, No
            let twoLinesMoment (x) = {
                guard x < DateTime("2026-08-01T00:00:00.000000001") else Ok
                guard x < DateTime("2026-08-01T00:00:00.000000002") else No
                Ok }

            behavior openOnBothSidesDense : (x: Decimal) -> Verdict
                constructs Ok, No
            let openOnBothSidesDense (x) = { guard x <= 1.0m else Ok
                guard x < 2.0m else No
                Ok }

            behavior openOnBothSidesMoment : (x: DateTime) -> Verdict
                constructs Ok, No
            let openOnBothSidesMoment (x) = {
                guard x <= DateTime("2026-08-01T00:00:00.000000001") else Ok
                guard x < DateTime("2026-08-01T00:00:00.000000002") else No
                Ok }
            """;

    /**
     * A {@code guard}'s line, at a bare position and at a newtype over the same values.
     *
     * <p>The line and the value beside it where the carrier steps; the line alone where it does not.
     * A {@code Decimal} and a {@code DateTime} have no smallest step this language names, so the row
     * beside the line is not asked for — which is a fact about the values and not about the reading,
     * and is why they are two obligations short of the whole numbers rather than unread.
     */
    @Test
    void aGuardsLineIsDrawnOnTheCarriersThatHaveACount() {
        Map<String, Measured> expected = new LinkedHashMap<>();
        expected.put("guardWholeBare", read(2));
        expected.put("guardDenseBare", read(1));
        expected.put("guardDayBare", read(2));
        expected.put("guardMomentBare", read(1));
        expected.put("guardTextBare", NO_CARRIER);
        expected.put("guardStageBare", NO_CARRIER_BUT_CLASSED);
        expected.put("guardWholeWrapped", read(2));
        expected.put("guardDenseWrapped", read(1));
        expected.put("guardDayWrapped", read(2));
        expected.put("guardMomentWrapped", read(1));
        expected.put("guardTextWrapped", NO_CARRIER);
        // Not what the bare position answers, and not what this row is about. A newtype over a sum
        // loses the sum's cases: the classes reader stops at the name instead of reading what it
        // wraps, so the position comes back as one the model divides no way. Written down as it is
        // rather than as it should be, because changing it is a different reader's work — and left
        // in the table so that fixing it is a cell that stops matching.
        expected.put("guardStageWrapped", NO_CARRIER);

        assertEquals(expected, measured(expected.keySet()));
    }

    /**
     * The same rule written as an invariant, which draws a line and no class.
     *
     * <p>Everything outside a bound is refused at construction, so there is no class on the far side
     * to cover and the position has one edge worth a row (ADR-0090) — which is why every cell here
     * has no axis and the {@code guard} cells above have one.
     */
    @Test
    void anInvariantsBoundIsDrawnOnTheSameCarriers() {
        Map<String, Measured> expected = new LinkedHashMap<>();
        expected.put("boundWhole", new Measured(0, 1, null));
        expected.put("boundDense", new Measured(0, 1, null));
        expected.put("boundDay", new Measured(0, 1, null));
        expected.put("boundMoment", new Measured(0, 1, null));
        expected.put("boundText", NO_CARRIER);
        expected.put("boundStage", NO_CARRIER);

        assertEquals(expected, measured(expected.keySet()));
    }

    /**
     * And the two rows say the same thing about the same carriers.
     *
     * <p>Asserted over the table rather than cell by cell, because what went wrong was not a wrong
     * number anywhere — it was one reader admitting a carrier the other refused, which only shows up
     * as two rows compared.
     */
    @Test
    void aCarrierIsReadOrNotWhicheverRuleWroteIt() {
        Map<String, Measured> all = measured(List.of(
                "guardWholeBare", "guardDenseBare", "guardDayBare", "guardMomentBare",
                "guardTextBare", "guardStageBare",
                "boundWhole", "boundDense", "boundDay", "boundMoment", "boundText", "boundStage"));

        for (String[] pair : new String[][] {
                {"guardWholeBare", "boundWhole"}, {"guardDenseBare", "boundDense"},
                {"guardDayBare", "boundDay"}, {"guardMomentBare", "boundMoment"},
                {"guardTextBare", "boundText"}, {"guardStageBare", "boundStage"}}) {
            assertEquals(all.get(pair[0]).unread(), all.get(pair[1]).unread(),
                    "a carrier a guard's line is drawn on is one an invariant's bound is drawn on: "
                            + pair[0] + " against " + pair[1]);
        }
    }

    /**
     * And a name wrapped round the values does not change the answer.
     *
     * <p>A newtype is the value it carries, so a rule about it is the rule about what it wraps. The
     * enumeration is left out here and not silently passed over: it is the one carrier where the two
     * forms disagree today, and the cell above says so.
     */
    @Test
    void aNameWrappedRoundTheValuesDoesNotChangeWhatIsMeasured() {
        Map<String, Measured> all = measured(List.of(
                "guardWholeBare", "guardDenseBare", "guardDayBare", "guardMomentBare",
                "guardTextBare",
                "guardWholeWrapped", "guardDenseWrapped", "guardDayWrapped", "guardMomentWrapped",
                "guardTextWrapped"));

        for (String carrier : List.of("Whole", "Dense", "Day", "Moment", "Text")) {
            assertEquals(all.get("guard" + carrier + "Bare"), all.get("guard" + carrier + "Wrapped"),
                    carrier + ": a newtype is the value it carries");
        }
    }

    /**
     * A class open at both ends offers a value of its own or none.
     *
     * <p>The pair of the test above, and the half of it that spacing alone gets wrong. Between two
     * decimals a whole apart there is a decimal; between two moments a nanosecond apart there is a
     * number and no date-time, because what a date-time can be written as sits on a grid at the
     * nanosecond however dense the carrier is for the purpose of sharpening a strict bound.
     *
     * <p>Read at the row and not at the count. What went wrong was not an arithmetic error — the
     * number offered was between the two ends — it was that writing it back landed on one of them,
     * so the row was labelled for a class it is not in, which is a row whose failure would show up
     * as the behavior answering with the wrong case.
     */
    @Test
    void aClassOpenAtBothEndsOffersAValueOfItsOwnOrNone() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();

        String dense = souther.compiler.report.GeneratedRows.of(
                compilation, "example.matrix", "openOnBothSidesDense", true);
        assertTrue(dense.contains("1.0 < x < 2.0"), dense);
        assertFalse(dense.contains("no value this position can hold"),
                "a decimal lies between two decimals a whole apart: " + dense);

        String moment = souther.compiler.report.GeneratedRows.of(
                compilation, "example.matrix", "openOnBothSidesMoment", true);
        assertTrue(moment.contains("no row for `x=2026-08-01T00:00:00.000000001 < x <"
                        + " 2026-08-01T00:00:00.000000002`"),
                "nothing lies strictly between two adjacent moments: " + moment);
        assertFalse(moment.contains(
                        "< x < 2026-08-01T00:00:00.000000002 x x = 2026-08-01T00:00:00.000000002"),
                "and no row is offered for that class carrying the value at its far end: " + moment);
    }

    /** What the measures answered for each named behavior. */
    private static Map<String, Measured> measured(Iterable<String> behaviors) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage("example.matrix")).value();
        assertNotNull(coverage, "the model under test compiles");

        Map<String, Measured> out = new LinkedHashMap<>();
        for (String behavior : behaviors) {
            PartitionEvidence evidence = coverage.get(behavior);
            assertNotNull(evidence, behavior + " was measured");
            String unread = evidence.unread().isEmpty() ? null
                    : said(evidence.unread().get(0).why());
            out.put(behavior, new Measured(evidence.axes().size(),
                    evidence.boundaries().size(), unread));
        }
        return out;
    }

    /** The reason as the report writes it, so a cell says what an author would read. */
    private static String said(UndividedPosition.Reason reason) {
        return switch (reason) {
            case UNSUPPORTED_SYNTAX -> "a comparison here is written in a form this does not read";
            case UNSUPPORTED_DOMAIN -> "it is compared against values no line can be drawn on here";
            case UNSUPPORTED_PARTITION_SHAPE ->
                    "the comparison relates it to another position rather than dividing it";
            case DEPTH_LIMIT -> "the walk stopped before reaching what is under it";
        };
    }

    /**
     * How the values step is the carrier's answer, and only the carrier's.
     *
     * <p>The class between two lines has a value in it where the values are dense, whatever they are
     * dense in: two decimals a whole apart and two moments a nanosecond apart both leave a range
     * holding something. Asked as "is this the decimal" it was a second spelling of the question,
     * and a carrier dense without being that one answered no — the range came back holding no value,
     * which is what a whole step would leave and not what the values do.
     */
    @Test
    void howTheValuesStepIsAskedOfTheCarrier() {
        for (String behavior : List.of("twoLinesDense", "twoLinesMoment")) {
            Compilation compilation = Compilation.ofSource(MODEL, "Main");
            compilation.measure(Adequacy.Asked.reportOnly());
            compilation.answerEverything();
            String block = souther.compiler.report.GeneratedRows.of(
                    compilation, "example.matrix", behavior, true);

            assertFalse(block.contains("no value of this range can be written"),
                    behavior + ": the range between the two lines holds a value: " + block);
            assertEquals(3, block.lines().filter(line -> line.contains(" : (")).count(),
                    behavior + ": a row for each of the three classes: " + block);
        }
    }
}
