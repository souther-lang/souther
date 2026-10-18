package souther.compiler;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A {@code match} on the element inside a walk's closure is a number of each element, chosen by the
 * case that element is, as the same {@code match} on one value is read case by case.
 *
 * <p>What is held here is that the total is one run over the container with each element's arm
 * chosen by its own case, that a field of one case is a place apart from a field of the same name in
 * another, that what the arms read is read as it is anywhere else in a closure, and that rows are
 * written for the line it draws.
 */
class AMatchOnTheElementInsideAWalkIsReadCaseByCaseTest {

    private static final String TWO_CASES = """
            data A = { amount: Int }
            data B = { amount: Int }
            data Deduction = A | B
            """;

    private static final String BY_CASE = """
            match d with
                    | A { amount } -> amount
                    | B { amount } -> amount""";

    private static final String READ_BY_CASE = "List.sum({when @A then 1·@A.amount + 0"
            + " when @B then 1·@B.amount + 0 | deductions[*]})";

    /** A guard that the deductions do not exceed the gross. */
    private static String guarded(String declarations, String closure) {
        return """
                module example.deductions

                %s

                data Exceeds

                behavior build : (gross: Int, deductions: List<Deduction>) -> Int | Exceeds

                let build (gross, deductions) = {
                    guard gross >= List.sum(List.map(d -> %s, deductions)) else Exceeds
                    gross
                }
                """.formatted(declarations, closure);
    }

    /** The same total against a number the model writes. */
    private static String thresholded(String declarations, String closure, int threshold) {
        return """
                module example.deductions

                %s

                data Many
                data Few

                behavior decide : (deductions: List<Deduction>) -> Many | Few

                let decide (deductions) =
                    if List.sum(List.map(d -> %s, deductions)) >= %d
                    then Many else Few
                """.formatted(declarations, closure, threshold);
    }

    @Test
    void theTotalIsReadAsTheArmEachElementTakes() {
        String report = report(guarded(TWO_CASES, BY_CASE));
        assertTrue(report.contains(READ_BY_CASE), report);
        assertFalse(report.contains("not read"), report);
    }

    /** Two cases declaring a field of one name are two places, each read where its case is. */
    @Test
    void aFieldOfOneCaseIsNotTheFieldOfTheSameNameInAnother() {
        String report = report(guarded(TWO_CASES, BY_CASE));
        assertTrue(report.contains("deductions[*]@A.amount"), report);
        assertTrue(report.contains("deductions[*]@B.amount"), report);
        assertFalse(report.contains("deductions[*].amount"), report);
    }

    @Test
    void fieldsOfTwoNamesAreReadEachUnderItsCase() {
        String report = report(guarded("""
                data A = { amount: Int }
                data B = { fee: Int, rate: Int }
                data Deduction = A | B
                """, """
                match d with
                        | A { amount } -> amount
                        | B { fee } -> fee * 2"""));
        assertTrue(report.contains("List.sum({when @A then 1·@A.amount + 0"
                + " when @B then 2·@B.fee + 0 | deductions[*]})"), report);
        assertFalse(report.contains("not read"), report);
    }

    /** A helper the {@code match} is written in, and a name given it, are the same number. */
    @Test
    void aHelperAndANameAreTheSameNumber() {
        String helper = report(guarded(TWO_CASES + """

                let amountOf (d: Deduction): Int = match d with
                    | A { amount } -> amount
                    | B { amount } -> amount
                """, "amountOf(d)"));
        assertTrue(helper.contains(READ_BY_CASE), helper);

        String named = report(guarded(TWO_CASES, """
                {
                            let owed = match d with
                                | A { amount } -> amount
                                | B { amount } -> amount
                            owed
                        }"""));
        assertTrue(named.contains(READ_BY_CASE), named);
    }

    /** A branch on a flag inside an arm is that case's choice, on the case's own flag. */
    @Test
    void aFlagInsideAnArmIsAFlagOfTheCase() {
        String report = report(guarded("""
                data A = { amount: Int, waived: Bool }
                data B = { amount: Int }
                data Deduction = A | B
                """, """
                match d with
                        | A { amount, waived } -> if waived then 0 else amount
                        | B { amount } -> amount"""));
        assertTrue(report.contains("List.sum({when @A then if @A.waived then 0 else 1·@A.amount + 0"
                + " when @B then 1·@B.amount + 0 | deductions[*]})"), report);
        assertFalse(report.contains("not read"), report);
    }

    /** A {@code match} inside an arm, on a field of the case, narrows that field. */
    @Test
    void aMatchInsideAnArmNarrowsAFieldOfTheCase() {
        String report = report(guarded("""
                data Statutory
                data Agreed
                data Kind = Statutory | Agreed
                data A = { amount: Int, kind: Kind }
                data B = { amount: Int }
                data Deduction = A | B
                """, """
                match d with
                        | A { amount, kind } -> match kind with
                            | Statutory -> amount
                            | Agreed -> 0
                        | B { amount } -> amount"""));
        assertTrue(report.contains("List.sum({when @A then when @A.kind@Statutory then"
                + " 1·@A.amount + 0 when @A.kind@Agreed then 0"
                + " when @B then 1·@B.amount + 0 | deductions[*]})"), report);
        assertFalse(report.contains("not read"), report);
    }

    /**
     * Arithmetic over a {@code match} is the {@code match} of the arithmetic: what is added to it is
     * added in each arm, and two of them in one sum are each chosen by their own case.
     */
    @Test
    void arithmeticOverAMatchIsTheMatchOfTheArithmetic() {
        String added = report(guarded(TWO_CASES, """
                (match d with
                        | A { amount } -> amount
                        | B { amount } -> amount) * 2 + 1"""));
        assertTrue(added.contains("List.sum({when @A then 2·@A.amount + 1"
                + " when @B then 2·@B.amount + 1 | deductions[*]})"), added);
        assertFalse(added.contains("not read"), added);

        String named = report(guarded(TWO_CASES, """
                {
                            let owed = match d with
                                | A { amount } -> amount
                                | B { amount } -> amount
                            1 + owed
                        }"""));
        assertTrue(named.contains("List.sum({when @A then 1·@A.amount + 1"
                + " when @B then 1·@B.amount + 1 | deductions[*]})"), named);
    }

    /** Every arm answering the same is an answer the case does not change. */
    @Test
    void armsThatAllAnswerAlikeAreThatAnswer() {
        String report = report(guarded(TWO_CASES, """
                match d with
                        | A { amount } -> 1
                        | B { amount } -> 1"""));
        assertFalse(report.contains("when @A"), report);
        assertFalse(report.contains("not read"), report);
    }

    /** An arm that is no form of the case's fields leaves the walk a rule nothing read. */
    @Test
    void anArmThatIsNoFormStaysUnread() {
        String report = report(guarded(TWO_CASES, """
                match d with
                        | A { amount } -> amount * amount
                        | B { amount } -> amount"""));
        assertTrue(report.contains("not read"), report);
        assertFalse(report.contains("List.sum({"), report);
    }

    /**
     * What each case guarantees of its own field bounds the total, and the widest of them is the
     * bound: both at or above nought leave nothing below nought, and one that reaches below nought
     * leaves it open though the other does not.
     */
    @Test
    void theTotalIsBoundedByWhatEveryCaseGuarantees() {
        String bothHeld = report(bounded("Amount"));
        assertTrue(bothHeld.contains("no OUT point is owed at List.sum({when @A then"
                + " 1·@A.amount + 0 when @B then 1·@B.fee + 0 | items[*]}) = 0"), bothHeld);

        String oneBelow = report(bounded("Credit"));
        assertTrue(oneBelow.contains("when @B then 1·@B.fee + 0 | items[*]}"), oneBelow);
        assertFalse(oneBelow.contains("no OUT point is owed at List.sum("), oneBelow);
    }

    /** Amounts at or above nought in {@code A}, and a fee of {@code feeType} in {@code B}. */
    private static String bounded(String feeType) {
        return """
                module example.bounded

                data Amount = Int
                    invariant value >= 0

                data Credit = Int
                    invariant value >= -5

                data A = { amount: Amount }
                data B = { fee: %s }
                data Item = A | B

                data Ok = { n: Int }
                data Bad

                let owed (i: Item): Int = match i with
                    | A { amount } -> amount.value
                    | B { fee } -> fee.value

                behavior settle : (items: List<Item>) -> Ok | Bad
                    constructs Ok

                let settle (items) = {
                    guard List.sum(List.map(i -> owed(i), items)) > 0 else Bad
                    Ok { n = 1 }
                }
                """.formatted(feeType);
    }

    /**
     * The rows written for the line come to what each point asks for, each element counted by its
     * own arm.
     */
    @Test
    void theRowsWrittenComeToTheTotalsThePointsAskFor() {
        String rows = rowsOf(thresholded(FEES, """
                match d with
                        | A { amount } -> amount
                        | B { fee } -> fee""", 6));
        List<Long> totals = totalsOf(rows, 1);

        assertTrue(totals.contains(6L), () -> "the point on the line: " + rows);
        assertTrue(totals.contains(5L), () -> "the point just off it: " + rows);
        assertTrue(totals.stream().anyMatch(each -> each > 6), () -> "one inside: " + rows);
    }

    /**
     * Every arm that is a form of one field of its case is tried, whichever is written first: twice
     * an amount is even, so no container of {@code A}s comes to five, and a {@code B} with a fee of
     * five does.
     */
    @Test
    void aPointOneCaseReachesIsWrittenWithThatCaseWhicheverArmComesFirst() {
        String rows = rowsOf(thresholded(FEES, """
                match d with
                        | A { amount } -> amount * 2
                        | B { fee } -> fee""", 6));
        assertTrue(rows.contains("""
                // fills OFF point of comparison@0:null
                    | ([B { fee = 5 }])"""), rows);
    }

    /**
     * A point only a container mixing the cases reaches is said as one this compiler did not try,
     * not as one no row comes to: an even number of each {@code A} and a multiple of three of each
     * {@code B} come to five only together.
     */
    @Test
    void aPointOnlyAMixOfCasesReachesIsLeftUntried() {
        Compilation compiled = compiled(thresholded(FEES, """
                match d with
                        | A { amount } -> amount * 2
                        | B { fee } -> fee * 3""", 6));
        String rows = rowsOf(compiled);
        assertTrue(rows.contains("no row for `List.sum({when @A then 2·@A.amount + 0"
                + " when @B then 3·@B.fee + 0 | deductions[*]}) = 5` in `decide`: the search left"
                + " something untried"), rows);
        String report = report(compiled);
        assertTrue(report.lines().anyMatch(line -> line.contains("= 5 — ")
                && line.contains("the containers mixing the cases a computed number is chosen by"
                        + " rather than all of them")),
                report);
    }

    /**
     * A sum worn under a newtype is matched as the case it wraps, and the rows written for it read
     * back as the totals they were written for.
     */
    @Test
    void aSumWornUnderANewtypeIsMatchedAsTheCaseItWraps() {
        String rows = rowsOf(thresholded("""
                data A = { amount: Int }
                data B = { amount: Int }
                data Owed = A | B
                data Deduction = Owed
                """, """
                match d.value with
                        | A { amount } -> amount
                        | B { amount } -> amount""", 6));
        assertTrue(rows.contains("fills ON point"), rows);
        assertFalse(rows.contains("= 6` in `decide`"), rows);
    }

    /**
     * Arms that each answer a number written in the arm are chosen by the carrier the optional is
     * at: no field read afterwards could catch the wrong arm, so the rows read back are what holds
     * the choice to the program's. A line holding a cap comes to one and stands at the point below
     * the line, and a line holding none comes to nought and stands outside it.
     */
    @Test
    void armsAnsweringWrittenNumbersAreChosenByTheOptionalsCarrier() {
        Compilation compiled = compiled("""
                module example.capped

                data Line = { cap: Option<Int> }

                data Many
                data Few

                behavior decide : (lines: List<Line>) -> Many | Few

                let decide (lines) =
                    if List.sum(List.map(l -> match l.cap with
                            | Some n -> 1
                            | None -> 0, lines)) >= 2
                    then Many else Few
                """);
        String report = report(compiled);
        assertTrue(report.contains("when cap@Some then 1 when cap@None then 0 | lines[*]"),
                report);
        assertFalse(report.contains("not read"), report);
        String rows = rowsOf(compiled);
        assertTrue(rows.contains("""
                // fills OFF point of comparison@0:null
                    | "lines[*].cap=Some" : ([Line { cap = 0 }])"""), rows);
        assertTrue(rows.contains("""
                // fills OUT point of comparison@0:null
                    | "lines[*].cap=None" : ([Line { cap = None }])"""), rows);
    }

    private static final String FEES = """
            data A = { amount: Int }
            data B = { fee: Int }
            data Deduction = A | B
            """;

    /** What each row's elements come to, an {@code A} at its amount weighed {@code weight} and a
     *  {@code B} at its fee. */
    private static List<Long> totalsOf(String rows, long weight) {
        List<Long> totals = new ArrayList<>();
        Pattern element = Pattern.compile("(A \\{ amount|B \\{ fee) = (-?\\d+)");
        for (String row : rows.split("\n    \\| ")) {
            Matcher found = element.matcher(row);
            long total = 0;
            boolean any = false;
            while (found.find()) {
                long held = Long.parseLong(found.group(2));
                total += found.group(1).startsWith("A") ? weight * held : held;
                any = true;
            }
            if (any) {
                totals.add(total);
            }
        }
        return totals;
    }

    private static String rowsOf(String model) {
        return rowsOf(compiled(model));
    }

    private static String rowsOf(Compilation compilation) {
        return GeneratedRows.of(compilation, null, null,
                SourceRendering.namedByIdentity(SourceLayouts.NONE)).text();
    }

    private static String report(String model) {
        return report(compiled(model));
    }

    private static String report(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static Compilation compiled(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
