package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Located;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.GeneratedRows;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A type invariant that chooses between two ranges leaves its position the two ranges, and a value
 * chosen for the position is one of them.
 *
 * <p>Ranges far from where a value is usually chosen, so a row exists only where the choice reached
 * whoever chooses: zero for a number, and the day the rows are written on for a date, both fall in
 * the gap.
 */
class ATypeInvariantChoosingBetweenRangesLeavesAValueInOneOfThemTest {

    private static final String BESIDE_ANOTHER_INPUT = """
            behavior f : (u: U, n: Int) -> Bool
            let f (u, n) = if n >= 3 then true else false
            """;

    private static String model(String type, String invariant, String behavior) {
        return """
                module example.gap

                data U = TYPE
                    invariant RULE

                """.replace("TYPE", type).replace("RULE", invariant) + behavior;
    }

    private static String blockFor(String type, String invariant, String behavior) {
        Compilation compilation = Compilation.ofSource(model(type, invariant, behavior), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return GeneratedRows.of(compilation, "example.gap", "f",
                SourceRendering.namedByIdentity(compilation.texts())).text();
    }

    private static List<String> codesFor(String type, String invariant) {
        Compilation compilation = Compilation.ofSource(
                model(type, invariant, BESIDE_ANOTHER_INPUT), "Main");
        compilation.answerEverything();
        return compilation.diagnostics().values().stream()
                .flatMap(List::stream)
                .map(Located::diagnostic)
                .map(diagnostic -> diagnostic.code())
                .toList();
    }

    @Test
    void aNumberGetsARowForEveryClassOfTheOtherPosition() {
        String block = blockFor("Int", "value > 100 || value < 0", BESIDE_ANOTHER_INPUT);

        assertFalse(block.contains("no row for"), block);
        assertTrue(block.contains("n=x < 3"), block);
        assertTrue(block.contains("n=3 <= x"), block);
    }

    @Test
    void aDateGetsARowForEveryClassOfTheOtherPosition() {
        String block = blockFor("Date",
                "value > Date(\"2300-01-01\") || value < Date(\"1900-01-01\")",
                BESIDE_ANOTHER_INPUT);

        assertFalse(block.contains("no row for"), block);
        assertTrue(block.contains("n=x < 3"), block);
        assertTrue(block.contains("n=3 <= x"), block);
    }

    /**
     * A body that draws its line in the gap gets a row on each side of it, each the value of the
     * run on that side nearest the line: the values beside the line are the gap's, and neither is a
     * value of the type — which is said of the points at the line, and not that their values were
     * refused.
     */
    @Test
    void aBodyDrawingItsLineInTheGapGetsARowInEachRun() {
        String block = blockFor("Int", "value > 100 || value < 0", """
                behavior f : (u: U) -> Bool
                let f (u) = if u.value > 50 then true else false
                """);

        assertTrue(block.contains("(U(-1))"), block);
        assertTrue(block.contains("(U(101))"), block);
        assertFalse(block.contains("refused at construction"), block);
        assertTrue(block.contains("no row for `u = 50` in `f`: no value can stand here"), block);
        assertTrue(block.contains("no row for `u = 51` in `f`: no value can stand here"), block);
    }

    private static String blockOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return GeneratedRows.of(compilation, "example.gap", "f",
                SourceRendering.namedByIdentity(compilation.texts())).text();
    }

    /** A choice of ranges above a sum whose case {@code A} states {@code CASE} of the shared
     *  field, read by a behavior that owes nothing but the lines the declarations draw. */
    private static final String ABOVE_A_SUM = """
            module example.gap

            data Paging = { limit: Int }
            data A = { ...Paging, x: Int }
                invariant own = CASE
            data B = { ...Paging, y: Int }
            data Q = A | B

            data Holder = { q: Q }
                invariant apart = q.limit > 100 || q.limit < 0

            behavior f : (h: Holder) -> Bool
            let f (h) = true
            """;

    /**
     * A case whose own rule leaves one of the runs above is written in that run, and the line its
     * rule draws in the gap is one no value stands at — not one whose values were refused, which
     * is what choosing between the ends around both runs came to.
     */
    @Test
    void aCaseLeavingOneOfTheRunsAboveIsWrittenInThatRun() {
        String block = blockOf(ABOVE_A_SUM.replace("CASE", "limit >= 0"));

        assertTrue(block.contains("A { limit = 101"), block);
        assertTrue(block.contains("no row can be written at `limit = 0` owed by `A`: every reading"
                + " of the line was searched and no value can stand at it"), block);
        assertFalse(block.contains("refused at construction"), block);
        assertFalse(block.contains("nothing here could build"), block);
    }

    /**
     * A case whose own rule leaves neither run is one no value of the field stands in, which is
     * said of every line its rule draws — and not the range its rule states, offered again.
     */
    @Test
    void aCaseLeavingNeitherRunAboveHoldsNoValueAtItsLines() {
        String block = blockOf(ABOVE_A_SUM.replace("CASE", "limit >= 0 && limit <= 100"));

        assertTrue(block.contains("no row can be written at `limit in 0 < limit <= 100` owed by"
                + " `A`: every reading of the line was searched and no value can stand at it"),
                block);
        assertFalse(block.contains("the search left something untried"), block);
        assertFalse(block.contains("nothing here could build"), block);
    }

    /**
     * A value a rule singles out leaves the two runs either side of it, and every position with
     * such a hole is written in one of them — so a record of many of them is one row, and not a
     * search through every pairing of the values beside each hole.
     */
    @Test
    void positionsEachWithAHoleAreWrittenBesideTheirHoles() {
        StringBuilder fields = new StringBuilder("    { a1: Int\n");
        StringBuilder rule = new StringBuilder("a1 /= 0");
        for (int i = 2; i <= 11; i++) {
            fields.append("    , a").append(i).append(": Int\n");
            rule.append(" && a").append(i).append(" /= 0");
        }
        String block = blockOf("""
                module example.gap

                data R =
                FIELDS    }
                    invariant rule = RULE

                data Ok

                behavior f : (r: R, flag: Bool) -> Ok

                let f (r, flag) = if flag then Ok else Ok
                """.replace("FIELDS", fields.toString()).replace("RULE", rule.toString()));

        assertTrue(block.contains("a11 = 1"), block);
        assertFalse(block.contains("no row for"), block);
    }

    /**
     * A rule of the value above a sum about a field its cases share holds a value of the sum built
     * for a row that decides nothing under it — the value is planned under a case, and its field is
     * held to that rule as well as to the case's own.
     */
    @Test
    void aRuleAboveASumHoldsTheCaseAValueIsBuiltAs() {
        String block = blockOf(ABOVE_A_SUM.replace("CASE", "limit >= 0")
                .replace("q.limit > 100 || q.limit < 0", "q.limit > 100")
                .replace("behavior f : (h: Holder) -> Bool", "behavior f : (h: Holder, n: Int) -> Bool")
                .replace("let f (h) = true", "let f (h, n) = if n >= 3 then true else false"));

        assertTrue(block.contains("fills ON point"), block);
        assertTrue(block.contains("A { limit = 101"), block);
        assertFalse(block.contains("no row for"), block);
    }

    /**
     * And so does a value of the sum built whole, as the elements of a list beside the first are:
     * the case is built field by field, each field held to the rule above as well.
     */
    @Test
    void aRuleAboveASumHoldsTheCaseOfAnElementBuiltWhole() {
        String block = blockOf(ABOVE_A_SUM.replace("CASE", "limit >= 0")
                .replace("q.limit > 100 || q.limit < 0", "q.limit > 100")
                .replace("behavior f : (h: Holder) -> Bool", """
                        data Holders = List<Holder>
                            invariant nonEmpty = List.length(value) >= 1

                        behavior f : (hs: Holders, n: Int) -> Bool""")
                .replace("let f (h) = true", "let f (hs, n) = if n >= 3 then true else false"));

        assertFalse(block.contains("no row for"), block);
    }

    /** The same of a record inside a record built whole: a rule naming the inner record's field
     *  holds it there. */
    @Test
    void aRuleNamingAFieldOfAnInnerRecordHoldsItWhenTheOuterIsBuiltWhole() {
        String block = blockOf("""
                module example.gap

                data Paging = { limit: Int }
                    invariant own = limit >= 0
                data Holder = { p: Paging }
                    invariant above = p.limit > 100
                data Holders = List<Holder>
                    invariant nonEmpty = List.length(value) >= 1

                behavior f : (hs: Holders, n: Int) -> Bool
                let f (hs, n) = if n >= 3 then true else false
                """);

        assertFalse(block.contains("no row for"), block);
    }

    /** One declaration's choice cut to one run by a rule beside it is written in that run. */
    @Test
    void aChoiceCutToOneRunByTheRuleBesideItIsWrittenInThatRun() {
        String block = blockFor("Int", "(value > 100 || value < 0) && value >= 0",
                BESIDE_ANOTHER_INPUT);

        assertFalse(block.contains("no row for"), block);
    }

    /** A value held to a class of residues is a member in one of the runs, either side of a line
     *  drawn in the gap. */
    @Test
    void aClassOfResiduesBesideALineInTheGapIsWrittenInARun() {
        String block = blockFor("Int", "value % 2 == 0 && (value > 100 || value < 0)", """
                behavior f : (u: U) -> Bool
                let f (u) = if u.value > 50 then true else false
                """);

        assertFalse(block.contains("refused at construction"), block);
    }

    /**
     * A value standing for a class is one the position's values take in: the value nearest where
     * the number is usually near is one a rule may single out, and a class stood for by it would
     * have no row.
     */
    @Test
    void theValueStandingForAClassIsOneThePositionTakes() {
        String block = blockFor("Int", "(value > 100 || value < 0) && value /= -1", """
                behavior f : (u: U) -> Bool
                let f (u) = if u.value > 50 then true else false
                """);

        assertTrue(block.contains("(U(-2))"), block);
        assertFalse(block.contains("refused at construction"), block);
    }

    /** A choice whose ranges a rule beside it leaves no value of is refused where it is written. */
    @Test
    void aChoiceTheRestOfTheRulesLeaveNothingOfIsRefused() {
        assertEquals(List.of("E1013"),
                codesFor("Int", "(value > 100 || value < 0) && value >= 0 && value <= 100"));
        assertEquals(List.of(),
                codesFor("Int", "(value > 100 || value < 0) && value >= 0 && value <= 101"),
                "one value is left, and it is a value of the type");
    }
}
