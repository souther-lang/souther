package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@code guard} comparing one position against another draws a line, and the rows are owed it.
 *
 * <p>The line is where the two are equal. A guard's arms are above the line and below-or-on it, so a
 * row on the line takes the same arm as one well below it, and the arms cannot stand in for it — a
 * row on the line is the one thing that tells a rule written {@code >} from one written {@code >=}
 * (spec §every-guard-boundary-has-a-row).
 *
 * <p>Nothing asked for it. The reader that turns a comparison into a line wants a constant on one
 * side, and where there is none it produced nothing at all: no line, no obligation, and a note saying
 * the partition could not read the comparison — which is not a demand and is counted nowhere. So a
 * model whose every rule is of this shape reported every measure full and {@code --strict} exited
 * {@code 0} while nothing had ever been evaluated at the line each rule turns on.
 *
 * <p>Which positions those are is asked of the carrier and not of the type. Two operands compare only
 * when they are of one type, and a type is not what makes a line measurable: a {@code String} is
 * ordered and has no count to embed into, so it draws no line of this kind until it has a carrier.
 */
class ALineBetweenTwoPositionsIsStillALineTest {

    /** The shape the defect was found in: a charge against a ceiling, each a newtype of its own with
     *  a minimum of its own, so no invariant row lands on the diagonal by coincidence. */
    private static final String TWO_NEWTYPES = """
            module example.relational

            data Charge = Int
                invariant value >= 0
            data Ceiling = Int
                invariant value >= 1000

            data NoBenefit
            data Benefit = { amount: Charge }
            data Result = NoBenefit | Benefit

            behavior benefitOf : (charge: Charge, ceiling: Ceiling) -> Result
                constructs NoBenefit, Benefit, Charge
            let benefitOf (charge, ceiling) = {
                guard charge.value > ceiling.value else NoBenefit
                Benefit { amount = Charge(charge.value - ceiling.value) }
            }

            example benefitOf
                | "over the ceiling" : (Charge(100000), Ceiling(80000))
                    -> Benefit { amount = Charge(20000) }
                | "under the ceiling" : (Charge(50000), Ceiling(80000)) -> NoBenefit
                | "charge = 0 x ceiling = 1000" : (Charge(0), Ceiling(1000)) -> NoBenefit
            """;

    /** The same with a row on the line. Under `>` a charge equal to the ceiling is no benefit; under
     *  `>=` it is a benefit of nothing, so this row is what tells the two apart. */
    private static final String ON_THE_LINE = TWO_NEWTYPES
            + "    | \"at the ceiling\" : (Charge(1000), Ceiling(1000)) -> NoBenefit\n";

    /** Two plain {@code Int} parameters. Nothing bounds either of them, so the behavior has no axis
     *  at all — and the line its body draws is still a line. */
    private static final String NO_AXIS = """
            module example.bare

            data NoBenefit
            data Benefit = { amount: Int }
            data Result = NoBenefit | Benefit

            behavior benefitOf : (charge: Int, ceiling: Int) -> Result
                constructs NoBenefit, Benefit
            let benefitOf (charge, ceiling) = {
                guard charge > ceiling else NoBenefit
                Benefit { amount = charge - ceiling }
            }

            example benefitOf
                | "over" : (100000, 80000) -> Benefit { amount = 20000 }
                | "under" : (50000, 80000) -> NoBenefit
            """;

    /** Two positions of one enumeration, which counts on the place its cases are declared at. */
    private static final String ENUMERATION = """
            module example.rank

            data Bronze
            data Silver
            data Gold
            data Rank = Bronze | Silver | Gold

            data No
            data Yes = { r: Rank }
            data Result = No | Yes

            behavior cmp : (a: Rank, b: Rank) -> Result
                constructs No, Yes
            let cmp (a, b) = {
                guard a > b else No
                Yes { r = a }
            }

            example cmp
                | "over" : (Gold, Bronze) -> Yes { r = Gold }
                | "under" : (Bronze, Gold) -> No
            """;

    /** Two {@code String} positions. Ordered, comparable, and counting on nothing. */
    private static final String NO_CARRIER = """
            module example.text

            data No
            data Yes = { s: String }
            data Result = No | Yes

            behavior cmp : (a: String, b: String) -> Result
                constructs No, Yes
            let cmp (a, b) = {
                guard a > b else No
                Yes { s = a }
            }

            example cmp
                | "over" : ("m", "b") -> Yes { s = "m" }
                | "under" : ("b", "m") -> No
            """;

    /** An expression on one side, which names no position a row can be written at. */
    private static final String NOT_A_TERM = """
            module example.offset

            data NoBenefit
            data Benefit = { amount: Int }
            data Result = NoBenefit | Benefit

            behavior benefitOf : (charge: Int, ceiling: Int) -> Result
                constructs NoBenefit, Benefit
            let benefitOf (charge, ceiling) = {
                guard charge > ceiling + 1000 else NoBenefit
                Benefit { amount = charge - ceiling }
            }

            example benefitOf
                | "over" : (100000, 80000) -> Benefit { amount = 20000 }
                | "under" : (50000, 80000) -> NoBenefit
            """;

    /** Two positions whose minima leave them no count in common. */
    private static final String NO_COMMON_COUNT = """
            module example.apart

            data Low = Int
                invariant value <= -1
            data High = Int
                invariant value >= 1

            data No
            data Yes = { v: Low }
            data Result = No | Yes

            behavior cmp : (a: Low, b: High) -> Result
                constructs No, Yes
            let cmp (a, b) = {
                guard a.value > b.value else No
                Yes { v = a }
            }

            example cmp
                | "under" : (Low(-5), High(5)) -> No
            """;

    @Test
    void aComparisonOfTwoPositionsAsksForARowWhereTheyAreEqual() {
        String report = report(TWO_NEWTYPES);

        assertTrue(report.contains("no row is at benefitOf/charge = ceiling"), report);
        assertTrue(report.contains("boundary    2/3"), report);
    }

    /** The row on the line meets it, and the line is met by a row that reached the comparison — the
     *  same rule a line against a constant is met by. */
    @Test
    void aRowOnTheLineMeetsIt() {
        String report = report(ON_THE_LINE);

        assertTrue(report.contains("boundary    3/3"), report);
        assertFalse(report.contains("no row is at benefitOf/charge = ceiling"), report);
    }

    /**
     * The line is not the axis's, so a behavior with no axis has one all the same.
     *
     * <p>This is the case the old reading cannot be patched into. There is no position here for a line
     * to be a count of: two plain {@code Int} parameters have no invariant, no threshold and no axis,
     * and the body still draws a line between them.
     */
    @Test
    void aBehaviorWithNoAxisStillDrawsALineBetweenItsPositions() {
        String report = report(NO_AXIS);

        assertTrue(report.contains("no row is at benefitOf/charge = ceiling"), report);
        assertTrue(report.contains("boundary    0/1"), report);
    }

    /** An enumeration counts on the place its cases are declared at, so it reaches this by the same
     *  route a number does. */
    @Test
    void anEnumerationDrawsOneToo() {
        String report = report(ENUMERATION);

        assertTrue(report.contains("no row is at cmp/a = b"), report);
    }

    /** Recognised by the carrier and not by the type: `String` is ordered, compares, and counts on
     *  nothing, so no line of this kind is drawn on it. */
    @Test
    void aCarrierlessTypeDrawsNone() {
        String report = report(NO_CARRIER);

        assertFalse(report.contains("no row is at cmp/a = b"), report);
        assertTrue(report.contains("boundary    not measured (no line was derived at any position)"),
                report);
    }

    /** One side has to be a position and not something taken of one. Where it is not, the line is
     *  where the difference is a constant, which is not a place either position can be asked for. */
    @Test
    void anOperandThatIsNotAPositionDrawsNone() {
        String report = report(NOT_A_TERM);

        assertFalse(report.contains("no row is at"), report);
        assertTrue(report.contains("not read: charge"), report);
    }

    /**
     * A line no count satisfies is reported and not counted.
     *
     * <p>The rules leave the two positions nothing in common, so no row can be on the line. That is
     * not a row anybody is owed and not a gap a build is refused over — and it is still the only thing
     * there is to say about the comparison, so it is said.
     */
    @Test
    void aLineNoCountSatisfiesIsSaidAndNotCounted() {
        String report = report(NO_COMMON_COUNT);

        assertTrue(report.contains("not known to be writable: cmp/a = b"), report);
        assertFalse(report.contains("no row is at cmp/a = b"), report);
    }

    /**
     * The partition is unchanged and says so where it is.
     *
     * <p>A rule relating two positions divides neither of them, which is what the classes measure has
     * always answered here and still answers. The two are separate answers about one comparison, and
     * the note about the first of them belongs under the first of them — printed under the boundary
     * count it sat two rows beneath the line that same comparison had drawn.
     */
    @Test
    void thePositionIsStillOneNothingDividesAndTheNoteIsUnderThePartition() {
        String report = report(TWO_NEWTYPES);

        int partition = report.indexOf("    partition ");
        int note = report.indexOf("· not read: charge");
        int boundary = report.indexOf("    boundary ");

        assertTrue(note > partition && note < boundary,
                "the note about the classes sits under the classes measure:\n" + report);
        assertTrue(report.contains(
                "not read: charge (the comparison relates it to another position"
                        + " rather than dividing it)"), report);
    }

    /**
     * The row offered for such a line puts one value at both positions.
     *
     * <p>Which is the whole of what makes it a row on the line. A search that settled one position
     * and left the other to its own range would offer a row beside the line as readily as one on it,
     * and the row a person is handed is the one they answer.
     */
    @Test
    void theRowOfferedForTheLinePutsOneValueAtBothPositions() {
        String rows = generated(TWO_NEWTYPES);

        assertTrue(rows.contains("(Charge(1000), Ceiling(1000))"), rows);
    }

    /** A count both positions admit is what the offer is written at, and where the rules leave none
     *  there is no offer — and no claim that the line cannot be written on either. */
    @Test
    void aLineNoCountSatisfiesIsOfferedNoRowAndCalledNoNames() {
        String rows = generated(NO_COMMON_COUNT);

        assertTrue(rows.contains("no row for `a = b`"), rows);
        assertTrue(rows.contains("does not make the edge unwritable"), rows);
    }

    private static String report(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).human(SourceNameResolver.identity());
    }

    private static String generated(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return souther.compiler.report.GeneratedRows.of(compilation, null, null, true,
                SourceNameResolver.identity());
    }

    /** Held here so a rename of the report's own words does not quietly turn every assertion above
     * into one that passes on a report saying nothing. */
    @Test
    void theReportStillNamesTheMeasuresTheseAssertionsRead() {
        String report = report(TWO_NEWTYPES);

        assertEquals(1, report.split("    boundary ", -1).length - 1, report);
        assertEquals(1, report.split("    partition ", -1).length - 1, report);
    }
}
