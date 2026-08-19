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
 * when they are of one type, and a type is not what makes a line measurable: two newtypes of one base
 * are two types ordered alike and have a line, while two positions each declared as one case of an
 * enumeration are comparable on their sum's order, range over less than it, and have none.
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

    /** Two {@code String} positions, which order on their own values. */
    private static final String TEXT = """
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

    /** Two positions declared as cases of one sum. They compare, because the sum lists them both,
     *  and a case is not an enumeration: neither carries places of its own. */
    private static final String NO_CARRIER = """
            module example.caserel

            data Bronze
            data Silver
            data Gold
            data Rank = Bronze | Silver | Gold

            data No
            data Yes = { r: Rank }
            data Result = No | Yes

            behavior cmp : (a: Bronze, b: Gold) -> Result
                constructs No, Yes
            let cmp (a, b) = {
                guard a > b else No
                Yes { r = a }
            }

            example cmp
                | "under" : (Bronze, Gold) -> No
            """;

    /** A measure of each position rather than each position. Both sides are lengths, which are whole
     *  numbers, so the line is on the same order a number's is. */
    private static final String MEASURED = """
            module example.sized

            data No
            data Yes = { s: String }
            data Result = No | Yes

            behavior cmp : (a: String, b: String) -> Result
                constructs No, Yes
            let cmp (a, b) = {
                guard String.length(a) > String.length(b) else No
                Yes { s = a }
            }

            example cmp
                | "over" : ("mmm", "b") -> Yes { s = "mmm" }
                | "under" : ("b", "mmm") -> No
            """;

    /** Two fields of one record whose rule leaves the line between them no value at all. Each field's
     *  own range runs everywhere the other's does; no pair on the diagonal is in either. */
    private static final String RULED_OUT_BY_THE_RECORD = """
            module example.jointneg

            data Pair = { a: Int, b: Int }
                invariant a < b

            data No
            data Yes
            data Result = No | Yes

            behavior cmp : (p: Pair) -> Result
                constructs No, Yes
            let cmp (p) = {
                guard p.a > p.b else No
                Yes
            }

            example cmp
                | "under" : (Pair { a = 1, b = 5 }) -> No
            """;

    /** The same record one character apart, whose rule does admit the diagonal. */
    private static final String ALLOWED_BY_THE_RECORD =
            RULED_OUT_BY_THE_RECORD.replace("invariant a < b", "invariant a <= b");

    /** Two positions under different parameters whose rules the ranges cannot hold: a hole against a
     *  single value. Their ranges overlap at zero and one of them refuses zero. */
    private static final String A_HOLE_AND_A_POINT = """
            module example.holeneg

            data NonZero = Int
                invariant value /= 0

            data Zero = Int
                invariant value == 0

            data No
            data Yes
            data Result = No | Yes

            behavior cmp : (a: NonZero, b: Zero) -> Result
                constructs No, Yes
            let cmp (a, b) = {
                guard a.value > b.value else No
                Yes
            }

            example cmp
                | "over" : (NonZero(1), Zero(0)) -> Yes
                | "under" : (NonZero(-1), Zero(0)) -> No
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

        assertTrue(report.contains("no row is at the OFF point benefitOf/charge = ceiling"), report);
        assertTrue(report.contains("border      borders 3   coverage items 6/8   excluded 4"), report);
    }

    /**
     * The row on the line meets the point where the two terms meet, and is met by a row that reached
     * the comparison — the same rule a line against a constant is met by.
     *
     * <p>And meets that point alone. The border owes a row one step from the line as well, which is
     * a different pair: `charge > ceiling` is open where they meet, so the row on the line is the
     * point outside and the point inside is where the charge is one over. A reading that had them as
     * one set would call this border covered on the strength of a row that is at the other side of
     * it.
     */
    @Test
    void aRowOnTheLineMeetsIt() {
        String report = report(ON_THE_LINE);

        assertTrue(report.contains("border      borders 3   coverage items 7/8   excluded 4"), report);
        assertFalse(report.contains("no row is at the OFF point benefitOf/charge = ceiling ("),
                report);
        assertTrue(report.contains("no row is at the ON point benefitOf/charge = ceiling + 1"),
                report);
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

        assertTrue(report.contains("no row is at the OFF point benefitOf/charge = ceiling"), report);
        assertTrue(report.contains("border      borders 1   coverage items 2/4"), report);
    }

    /** An enumeration counts on the place its cases are declared at, so it reaches this by the same
     *  route a number does. */
    @Test
    void anEnumerationDrawsOneToo() {
        String report = report(ENUMERATION);

        assertTrue(report.contains("no row is at the OFF point cmp/a = b"), report);
    }

    /** A carrier whose values are strings reaches this the way one whose values count does. Nothing
     *  here is about numbers: the line is where the two positions hold the same place on one order. */
    @Test
    void aCarrierOfStringsDrawsOneToo() {
        String report = report(TEXT);

        assertTrue(report.contains("no row is at the OFF point cmp/a = b"), report);
    }

    /**
     * Recognised by the carrier and not by the type the comparison type-checked under.
     *
     * <p>Two cases of one sum order against each other — the sum lists them both — while neither is
     * an enumeration and neither carries places of its own. So the comparison is legal and the line
     * is not one anything can say where to write, and no line is drawn.
     */
    @Test
    void aComparableTypeWithNoCarrierDrawsNone() {
        String report = report(NO_CARRIER);

        assertFalse(report.contains("point cmp/a = b"), report);
        assertTrue(report.contains("border      not measured (no line was derived at any position)"),
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

        assertTrue(report.contains("not known to be writable: the OFF point cmp/a = b"), report);
        assertFalse(report.contains("no row is at the OFF point cmp/a = b"), report);
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
        int boundary = report.indexOf("    border ");

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
        assertTrue(rows.contains("does not make one unwritable"), rows);
    }

    /**
     * A line on a measure of two positions is drawn and read, and nothing here promises it.
     *
     * <p>Three answers and not one. The line is where the two lengths are equal and the rows can be
     * read against it; nothing here writes a value from a length — four is not what goes at the
     * position, it is four characters somebody has to choose — so no witness is found; and with no
     * witness nothing is counted.
     *
     * <p>What is said about that matters more than the absence. Two strings of one length are the
     * easiest row in the file to write by hand, so a sentence saying no value can be written there
     * would be false, and the one written says what this could not do.
     */
    @Test
    void aLineOnAMeasureIsReadAndPromisedByNothing() {
        String report = report(MEASURED);
        String rows = generated(MEASURED);

        assertFalse(report.contains("no row is at the OFF point cmp/String.length(a) = String.length(b)"), report);
        assertTrue(report.contains(
                "not known to be writable: the OFF point cmp/String.length(a) = String.length(b)"), report);
        assertTrue(rows.contains("nothing here could build a representative for it"), rows);
        assertTrue(rows.contains("does not make one unwritable"), rows);
    }

    /**
     * A rule the ranges could not take in is not a range that says nothing is missing.
     *
     * <p>{@code /= 0} leaves a hole and {@code == 0} leaves one value, and the two positions are
     * under different parameters, so nothing relates them and their ranges overlap at zero. Read as a
     * proof, that asks for a diagonal row at a value one of the two refuses outright.
     *
     * <p>Nor does "every rule was read" answer it. The checker understands a disequality perfectly
     * well and it reaches no range, so a position with a hole in it looks unbounded from there.
     */
    @Test
    void aRuleTheRangesCouldNotTakeInIsNotAProofEither() {
        String report = report(A_HOLE_AND_A_POINT);

        assertFalse(report.contains("no row is at the OFF point cmp/a = b"),
                "zero is the only place both ranges hold and one position refuses it:\n" + report);
        assertTrue(report.contains("not known to be writable: the OFF point cmp/a = b"), report);
    }

    /**
     * Two ranges overlapping is not two positions holding one value.
     *
     * <p>A place in both ranges is one each position admits on its own, and a rule relating them can
     * refuse the pair each half would have taken. Under {@code invariant a < b} the two ranges run
     * over each other everywhere and the diagonal holds nothing, so a projection read as a proof asks
     * for a row that cannot exist — and {@code --strict} refuses a model for not writing it.
     */
    @Test
    void aRuleRelatingTheTwoPositionsIsNotAnsweredByTheirRangesOverlapping() {
        String report = report(RULED_OUT_BY_THE_RECORD);

        assertFalse(report.contains("no row is at the OFF point cmp/p.a = p.b"),
                "the line holds no value, so no row is owed at it:\n" + report);
        assertTrue(report.contains("not known to be writable: the OFF point cmp/p.a = p.b"), report);
    }

    /**
     * And the same rule one character apart does owe the row.
     *
     * <p>The pair to the case above. Without it, refusing every line under a record that relates its
     * fields would pass just as well, and that would drop the rows the model does owe wherever an
     * author wrote a rule of any kind.
     */
    @Test
    void aRuleThatAdmitsTheDiagonalStillOwesTheRow() {
        String report = report(ALLOWED_BY_THE_RECORD);

        assertTrue(report.contains("no row is at the OFF point cmp/p.a = p.b"), report);
        assertTrue(report.contains("border      borders 1   coverage items 1/2"), report);
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

        assertEquals(1, report.split("    border ", -1).length - 1, report);
        assertEquals(1, report.split("    partition ", -1).length - 1, report);
    }
}
