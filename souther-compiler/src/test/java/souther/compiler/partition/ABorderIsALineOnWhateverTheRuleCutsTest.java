package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule draws a line wherever it cuts something the rows can be measured against, and what it cuts
 * is not always a position.
 *
 * <p>Issue #871. An equivalence partition is defined by conditions that may combine several
 * interacting variables, and each atomic condition defines a border of it (ISTQB CTAL-TA v4.0
 * §3.1.1). Souther drew a line where a rule compared one position against a written value, and where
 * it compared one position against another, and nothing anywhere else — so
 * {@code 300 * straw + 600 * choco <= 4800} drew nothing, and what the report showed instead were the
 * four sides of the box the two positions sit in. That is the case the technique exists for.
 *
 * <p>And the defect was wider than the issue's own title. {@code a + 1 <= 10} is a line at one
 * position, and {@code 2 * a <= 10} is a line on twice one position, and neither was read either:
 * what the readers wanted was a spelling, and what a rule says is arithmetic.
 *
 * <p>Two of these are the design tests rather than examples. {@code 2 * a <= 9} names a threshold the
 * quantity never takes — the even numbers have no nine in them — so a reading that assumed a
 * threshold is one of its quantity's own values puts a row at four and a half. And {@code a > b} over
 * strings has an order and no numbers, so a reading that turned every distance into a count loses it.
 * A border machinery that answers both without a branch for either is one a fourth kind of quantity
 * can be added to.
 */
class ABorderIsALineOnWhateverTheRuleCutsTest {

    /** Two whole-number positions, each bounded, so the box is finite and the search has ends. */
    private static String guarded(String condition) {
        return """
                module example.shape

                data Bound = Int
                    invariant value >= 0
                    invariant value <= 10

                data No = { why: Int }
                data Yes = { v: Int }
                data Result = No | Yes

                behavior f : (a: Bound, b: Bound) -> Result
                    constructs No, Yes
                let f (a, b) = {
                    guard %s else No { why = 0 }
                    Yes { v = 1 }
                }

                example f
                    | "one" : (Bound(1), Bound(1)) -> Yes { v = 1 }
                """.formatted(condition);
    }

    /** The issue's own model: a rule over what an order costs, and two positions it is priced on. */
    private static final String BASKET = """
            module example.basket

            data Strawberry = Int
                invariant value >= 0
                invariant value <= 10

            data Choco = Int
                invariant value >= 0
                invariant value <= 6

            data Order = { straw: Strawberry, choco: Choco }

            data TooExpensive = { total: Int }
            data Ok = { total: Int }
            data Result = TooExpensive | Ok

            let total (order: Order): Int =
                Int.add(Int.multiply(300, order.straw.value), Int.multiply(600, order.choco.value))

            behavior price : (order: Order) -> Result
                constructs TooExpensive, Ok
            let price (order) = {
                guard total(order) <= 4800 else TooExpensive { total = total(order) }
                Ok { total = total(order) }
            }

            example price
                | "cheap" : (Order { straw = Strawberry(1), choco = Choco(1) }) -> Ok { total = 900 }
            """;

    /** A bare position against a written value, which is the reading that always worked. */
    @Test
    void aPositionAgainstAValueIsALineAtThatPosition() {
        String report = report(guarded("a.value <= 10"));

        assertTrue(report.contains("point f/a = 10"), report);
    }

    /**
     * A constant added to the position moves the line rather than taking it away.
     *
     * <p>{@code a + 1 <= 10} is {@code a <= 9}, which is a line at one position and divides it into
     * classes — so this one reaches the partition measure as well as the border measure.
     */
    @Test
    void aConstantAddedToThePositionMovesTheLine() {
        String report = report(guarded("a.value + 1 <= 10"));

        assertTrue(report.contains("no row is at the ON point f/a = 9"), report);
        assertTrue(report.contains("no row is at the OFF point f/a = 10 (guard"), report);
        assertTrue(report.contains("equivalence partitions"),
                "a line at one position divides it:\n" + report);
    }

    /**
     * A position scaled is a quantity of its own, and the border is on that.
     *
     * <p>Not a line at {@code a}. What {@code 2 * a} takes is the even numbers, and the value past
     * ten is twelve — {@code a = 5} and {@code a = 6} are the rows, and the point they stand at is a
     * point of the form.
     */
    @Test
    void aScaledPositionIsAQuantityOfItsOwn() {
        String report = report(guarded("Int.multiply(2, a.value) <= 10"));

        assertTrue(report.contains("no row is at the ON point f/2 * a = 10"), report);
        assertTrue(report.contains("no row is at the OFF point f/2 * a = 12"), report);
    }

    /**
     * A threshold the quantity never takes still draws a border, either side of itself.
     *
     * <p>The design test. Nine is not a value {@code 2 * a} takes, and the rule cuts there all the
     * same: the row inside is where the form comes to eight and the row outside is where it comes to
     * ten. A reading that took the threshold for one of the quantity's own values would ask for a row
     * at nine — which is {@code a = 4.5}, a value the position refuses — and a reading that stepped
     * one from the threshold would ask for ten and eight in the wrong roles.
     */
    @Test
    void aThresholdTheQuantityNeverTakesStillDrawsABorder() {
        String report = report(guarded("Int.multiply(2, a.value) <= 9"));

        assertTrue(report.contains("no row is at the ON point f/2 * a = 8"), report);
        assertTrue(report.contains("no row is at the OFF point f/2 * a = 10"), report);
        assertFalse(report.contains("f/2 * a = 9"),
                "nine is not a value the quantity takes, so no row is asked for at it:\n" + report);
    }

    /** Both sides moving with the row, with a constant on one of them: a line on the distance, one
     *  along it. */
    @Test
    void aConstantOnOneSideOfARelationMovesTheLineAlongTheDistance() {
        String report = report(guarded("a.value + 1 > b.value"));

        assertTrue(report.contains("point f/a = b"), report);
        assertTrue(report.contains("point f/a = b - 1"), report);
    }

    /**
     * A form over two positions draws the line the model is about.
     *
     * <p>And the value past it is the next one the form takes rather than the next one any position
     * takes: {@code 3a + 6b} moves in threes, so the row outside {@code <= 48} is where it comes to
     * 51.
     */
    @Test
    void aFormOverTwoPositionsDrawsTheLineTheModelIsAbout() {
        String report = report(guarded(
                "Int.add(Int.multiply(3, a.value), Int.multiply(6, b.value)) <= 48"));

        assertTrue(report.contains("no row is at the ON point f/3 * a + 6 * b = 48"), report);
        assertTrue(report.contains("no row is at the OFF point f/3 * a + 6 * b = 51"), report);
    }

    /** A form on both sides is one form. What the rule states is the difference, so the position
     *  written on both sides is counted once. */
    @Test
    void aFormOnBothSidesIsOneForm() {
        String report = report(guarded(
                "Int.add(Int.multiply(3, a.value), Int.multiply(6, b.value))"
                        + " <= Int.add(b.value, 48)"));

        assertTrue(report.contains("no row is at the ON point f/3 * a + 5 * b = 48"), report);
    }

    /**
     * An order over strings is a border and carries no numbers.
     *
     * <p>The other design test. Two strings stand one above the other and no measurable distance
     * apart, so the only level the quantity takes is the one where they meet — and both sides of that
     * level are inhabited, because one string is still above another. A space that answered "no next
     * value" and "no value that way" with one word takes the {@code IN} point off this border; a
     * space that turned the distance into a count asks a carrier with no numbers to write one.
     */
    @Test
    void anOrderOverStringsIsABorderWithNoNumbersInIt() {
        String report = report("""
                module example.text

                data No = { why: Int }
                data Yes = { s: String }
                data Result = No | Yes

                behavior cmp : (a: String, b: String) -> Result
                    constructs No, Yes
                let cmp (a, b) = {
                    guard a > b else No { why = 0 }
                    Yes { s = a }
                }

                example cmp
                    | "over" : ("m", "b") -> Yes { s = "m" }
                    | "under" : ("b", "m") -> No { why = 0 }
                """);

        assertTrue(report.contains("no row is at the OFF point cmp/a = b"), report);
        assertTrue(report.contains("no ON point is owed at a = b")
                        && report.contains("name no neighbour"),
                "a string has no next string, so the point one along is not owed:\n" + report);
        assertFalse(report.contains("no IN point is owed") || report.contains("no OUT point is owed"),
                "and both sides of the line are still there, which is a different answer:\n"
                        + report);
    }

    /**
     * The issue's own model draws the border it is about, and the rows offered stand at it.
     *
     * <p>{@code (10, 3)} comes to 4800 and {@code (9, 4)} to 5100, which are the two points against
     * the line. Neither is a value of either position, and which position moved to reach them is the
     * search's answer rather than anything the report asks an author for.
     */
    @Test
    void theModelTheIssueWasWrittenAboutDrawsItsOwnBorder() {
        String report = report(BASKET);
        String rows = generated(BASKET);

        assertTrue(report.contains(
                "no row is at the ON point price/600 * order.choco + 300 * order.straw = 4800"),
                report);
        assertTrue(report.contains(
                "no row is at the OFF point price/600 * order.choco + 300 * order.straw = 5100"),
                report);
        assertTrue(rows.contains("Strawberry(10), choco = Choco(3)"), rows);
        assertTrue(rows.contains("Strawberry(9), choco = Choco(4)"), rows);
    }

    /**
     * A level the rules leave no row at is said to be out of reach, and not merely unfound.
     *
     * <p>The two are different facts and only one of them a reader may act on (ADR-0091). Here every
     * position is bounded and every combination of those bounds was walked, so a level nothing
     * reaches is a level the model refuses; a search that had stopped, or one that composed no
     * candidate at all, would say so in its own words.
     */
    @Test
    void aLevelTheRulesLeaveNoRowAtIsSaidToBeOutOfReach() {
        String report = report("""
                module example.narrow

                data Bound = Int
                    invariant value >= 6
                    invariant value <= 7

                data No = { why: Int }
                data Yes = { v: Int }
                data Result = No | Yes

                behavior f : (a: Bound) -> Result
                    constructs No, Yes
                let f (a) = {
                    guard Int.multiply(2, a.value) <= 9 else No { why = 0 }
                    Yes { v = 1 }
                }

                example f
                    | "one" : (Bound(6)) -> No { why = 0 }
                """);

        assertTrue(report.contains("the ON point f/2 * a = 8 (guard@14:5)"
                        + " — the rules leave no value at 2 * a = 8"), report);
        assertFalse(report.contains("nothing composed one: the rules leave no value"),
                "a proof does not arrive under the opening a failed search gets:\n" + report);
    }

    /** Two positions whose values fill: every distance is a distance, and no distance has a next
     *  one. */
    private static String dense(String condition) {
        return """
                module example.dense

                data D = Decimal
                    invariant value >= 0m
                    invariant value <= 100m

                data No = { why: Int }
                data Yes = { v: Int }
                data Result = No | Yes

                behavior f : (a: D, b: D) -> Result
                    constructs No, Yes
                let f (a, b) = {
                    guard %s else No { why = 0 }
                    Yes { v = 1 }
                }

                example f
                    | "under" : (D(1m), D(50m)) -> Yes { v = 1 }
                    | "over" : (D(50m), D(1m)) -> No { why = 0 }
                """.formatted(condition);
    }

    /**
     * A distance is a number, and it is one on an order with no smallest step too.
     *
     * <p>Two decimals a rule holds one apart are one apart. Read as a count of the carrier's steps
     * and reached by walking them, a carrier with no step answered "nowhere" for every pair — so the
     * border was met by no row, including the rows that meet it, and nothing could compose one.
     */
    @Test
    void aDistanceOverAnOrderWithNoStepIsStillADistance() {
        String report = report(dense("a.value <= b.value - 1m"));

        assertTrue(report.contains("point f/a = b - 1"), report);
        assertFalse(report.contains("nothing composed one"),
                "a pair one apart is composable over decimals:\n" + report);
    }

    /**
     * And it need not be a whole number of anything.
     *
     * <p>Held as a count of steps, a threshold of half a step was an {@code ArithmeticException}
     * thrown out of the measure rather than a rule read or refused.
     */
    @Test
    void aDistanceNeedNotBeAWholeNumberOfSteps() {
        String report = report(dense("a.value <= b.value - 0.5m"));

        assertTrue(report.contains("point f/a = b - 0.5"), report);
    }

    /**
     * The place a pair stands at answers to both positions at the distance the rule names.
     *
     * <p>Two positions each left {@code [0, 100]} have every place in common where the rule cuts
     * where they meet, and only {@code [1, 100]} where it holds them one apart — the pair at zero
     * puts the first at minus one, which its own rules refuse. Intersected without the distance, the
     * search offered exactly that pair and the report said every value tried had been refused.
     */
    @Test
    void thePlaceAPairStandsAtAnswersToBothPositionsAtThatDistance() {
        String report = report(dense("a.value <= b.value - 1m"));

        assertFalse(report.contains("was refused"),
                "the pair offered is one both positions admit:\n" + report);
    }

    /**
     * A form over positions whose values fill is not walked, and nothing is proved by not walking it.
     *
     * <p>{@code 2a + 4b = 9} holds at {@code a = 0.5, b = 2}. A search that enumerated the box one
     * whole number at a time missed it and reported that the rules leave no value there — which is
     * the one answer a reader may act on, so an unsound proof here is worse than an unsettled
     * search (ADR-0091).
     */
    @Test
    void aFormOverAnOrderThatFillsIsNotProvedEmptyByAWalkOverWholeNumbers() {
        String report = report(dense("a.value * 2m + b.value * 4m <= 9m"));

        assertTrue(report.contains("point f/2 * a + 4 * b = 9"), report);
        assertFalse(report.contains("the rules leave no value at 2 * a + 4 * b"),
                "nothing walked the whole of this box, so nothing was proved about it:\n" + report);
    }

    /**
     * A rule written the other way round is the same rule.
     *
     * <p>{@code 48 >= 3a + 6b} and {@code 3a + 6b <= 48} draw one line. Turned round in two of the
     * three readings and not the third, the first drew its border on {@code -3a - 6b} at
     * {@code -48} — the same four points under a name no author wrote, and a different line from the
     * rule written the other way.
     */
    @Test
    void aRuleWrittenTheOtherWayRoundIsTheSameRule() {
        String report = report(guarded(
                "48 >= Int.add(Int.multiply(3, a.value), Int.multiply(6, b.value))"));

        assertTrue(report.contains("no row is at the ON point f/3 * a + 6 * b = 48"), report);
        assertFalse(report.contains("-3 * a"), report);
    }

    /**
     * And a rule is read the same way wherever it is written.
     *
     * <p>Which quantity a comparison cuts was settled in three places, and the reading of a
     * behavior's clauses called two of them — so a form in an {@code ensures} drew no border while
     * the same form in a {@code guard} drew one.
     */
    @Test
    void aFormInAnEnsuresDrawsTheLineAFormInAGuardDraws() {
        String report = report("""
                module example.ens

                data Bound = Int
                    invariant value >= 0
                    invariant value <= 10

                data No = { why: Int }
                data Yes = { v: Int }
                data Result = No | Yes

                behavior f : (a: Bound, b: Bound) -> Result
                    ensures asked = Yes -> Int.add(Int.multiply(3, a.value),
                        Int.multiply(6, b.value)) <= 48

                example f
                    | "one" : (Bound(1), Bound(1)) -> Yes { v = 1 }
                """);

        assertTrue(report.contains("no row is at the ON point f/3 * a + 6 * b = 48"), report);
        assertTrue(report.contains("no row is at the OFF point f/3 * a + 6 * b = 51"), report);
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
        return GeneratedRows.of(compilation, null, null, true, SourceNameResolver.identity());
    }
}
