package souther.compiler;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A total of what a walk computed of each element by where the element stands is read as a line on
 * that total, and read over a row in the order the row writes the elements.
 *
 * <p>The weight of each element is a number chosen by its position, so the total relates the
 * elements and divides none of them, as a total of the elements themselves does. What tells the two
 * apart is the order: {@code [4, 2]} comes to ten weighed one and three by position, and
 * {@code [2, 4]} to fourteen, though the two hold the same values. So the rows here are ones a total
 * read without the order, or read from the other end, would put somewhere else.
 *
 * <p>And only there. A walk handed the elements in another order than the row's, a number that is
 * not the position, a weight that is arithmetic over the position: none is read as a choice by it.
 */
class ATotalWeighedByWhereEachElementStandsIsReadInTheOrderWrittenTest {

    private static final String TERM = "List.sum({if the position mod 2 == 0 then 1·the element"
            + " itself + 0 else 3·the element itself + 0 | xs[*]})";

    private static String model(String closure, String walked) {
        return """
                module p
                data Bad
                behavior check : (xs: List<Int>, n: Int) -> Int | Bad
                let check (xs, n) = {
                    guard List.sum(List.mapIndexed(%s, %s)) >= 10 else Bad
                    0
                }
                """.formatted(closure, walked);
    }

    private static final String BRANCH =
            "(i, c) -> if Int.floorMod(i, 2) == 0 then c else 3 * c";

    /** The total is read as a line, with the choice by position in its term. */
    @Test
    void aWeightChosenByThePositionIsReadAsALineOnTheTotal() {
        String human = report(model(BRANCH, "xs"));
        assertTrue(human.contains("no line: comparison") && human.contains(TERM), human);
        assertFalse(human.contains("not read:"), human);
    }

    /** The weight written as a factor is the same number, and the same term. */
    @Test
    void aWeightWrittenAsAFactorIsTheSameTerm() {
        String human = report(model(
                "(i, c) -> (if Int.floorMod(i, 2) == 0 then 1 else 3) * c", "xs"));
        assertTrue(human.contains(TERM), human);
        String flipped = report(model("(i, c) -> if 0 == Int.floorMod(i, 2) then c else 3 * c",
                "xs"));
        assertTrue(flipped.contains(TERM), flipped);
    }

    /** A closure bound to a name is the closure. */
    @Test
    void aClosureBehindANameIsReadTheSame() {
        String human = report("""
                module p
                data Bad
                behavior check : (xs: List<Int>, n: Int) -> Int | Bad
                let check (xs, n) = {
                    let weigh = %s
                    guard List.sum(List.mapIndexed(weigh, xs)) >= 10 else Bad
                    0
                }
                """.formatted(BRANCH));
        assertTrue(human.contains(TERM), human);
    }

    /** A choice whose answers are one answer turns on nothing, and is the total of the elements. */
    @Test
    void aChoiceThatAnswersAlikeIsNoChoice() {
        String human = report(model("(i, c) -> if Int.floorMod(i, 2) == 0 then c else c", "xs"));
        assertTrue(human.contains("List.sum(xs[*])"), human);
        assertFalse(human.contains("the position"), human);
    }

    /**
     * Elements handed in another order than the row's are not read by where they stand there, and
     * a total that does not turn on where they stand is read whatever their order.
     */
    @Test
    void aWalkOverTheElementsInAnotherOrderIsNotReadByPosition() {
        String reversed = report(model(BRANCH, "List.reverse(xs)"));
        assertTrue(reversed.contains("not read: comparison"), reversed);
        assertFalse(reversed.contains("the position"), reversed);
        String alike = report(model("(i, c) -> 3 * c", "List.reverse(xs)"));
        assertTrue(alike.contains("List.sum({3·the element itself + 0 | xs[*]})"), alike);
    }

    /** A whole number that is not the position is no position, and a weight that is arithmetic
     *  over the position is not a choice of it. */
    @Test
    void neitherAnotherNumberNorArithmeticOverThePositionIsAChoiceOfIt() {
        String another = report(model(
                "(i, c) -> if Int.floorMod(n, 2) == 0 then c else 3 * c", "xs"));
        assertTrue(another.contains("not read: comparison"), another);
        String product = report(model("(i, c) -> i * c", "xs"));
        assertTrue(product.contains("not read: comparison"), product);
    }

    /**
     * A row is read with its elements where it writes them. Weighed one and three by position,
     * {@code [4, 2]} is at ten and {@code [3, 2]} at nine, {@code [2, 4]} past the line and
     * {@code [4, 1]} short of it — and read without the order, or from the end, none of them is at
     * ten. So every point of the border is taken, and by these rows only on that reading.
     */
    @Test
    void aRowIsReadWithItsElementsWhereItWritesThem() {
        String human = report(model(BRANCH, "xs") + """
                example check
                    | "at"    : ([4, 2], 0) -> 0
                    | "below" : ([3, 2], 0) -> Bad
                    | "past"  : ([2, 4], 0) -> 0
                    | "short" : ([4, 1], 0) -> Bad
                """);
        assertTrue(human.contains("obligations 4/4"), human);
        assertFalse(human.contains("undecided whether a row is at"), human);
    }

    /** A model of elements holding a number and a flag, totalled by {@code closure}, with
     *  {@code rows}. */
    private static String items(String closure, String rows) {
        return """
                module p
                data Bad
                data Item = { q: Int, debit: Bool }
                behavior check : (xs: List<Item>) -> Int | Bad
                let check (xs) = {
                    guard List.sum(List.mapIndexed(%s, xs)) >= 10 else Bad
                    0
                }
                example check
                %s""".formatted(closure, rows.indent(4));
    }

    private static String item(long q, boolean debit) {
        return "Item { q = " + q + ", debit = " + debit + " }";
    }

    /** Every point of the border taken by the rows, which the runs hold to their answers. */
    private static void everyPointIsTaken(String human) {
        assertTrue(human.contains("obligations 4/4"), human);
        assertFalse(human.contains("undecided whether a row is at"), human);
        assertFalse(human.contains("does not hold"), human);
    }

    /**
     * A choice by position inside a choice by a flag is made for each element by both: the flag
     * first, and the position where the flag chose it. Without the position the rows below are
     * six, five, six and four; without the flag the last is seven.
     */
    @Test
    void aChoiceByPositionInsideAChoiceByAFlagIsMadeByBoth() {
        everyPointIsTaken(report(items(
                "(i, c) -> if c.debit then (if Int.floorMod(i, 2) == 0 then c.q else 3 * c.q)"
                        + " else 0",
                "| \"at\"    : ([" + item(4, true) + ", " + item(2, true) + "]) -> 0\n"
                        + "| \"below\" : ([" + item(3, true) + ", " + item(2, true) + "]) -> Bad\n"
                        + "| \"past\"  : ([" + item(2, true) + ", " + item(4, true) + "]) -> 0\n"
                        + "| \"short\" : ([" + item(4, true) + ", " + item(1, false)
                        + "]) -> Bad\n")));
    }

    /** A choice by position added to a choice by a flag is each made for the element on its own,
     *  and added. */
    @Test
    void aChoiceByPositionAddedToAChoiceByAFlagIsBothAddedUp() {
        String closure = "(i, c) -> (if Int.floorMod(i, 2) == 0 then c.q else 3 * c.q)"
                + " + (if c.debit then 1 else 0)";
        everyPointIsTaken(report(items(closure,
                "| \"at\"    : ([" + item(4, false) + ", " + item(2, false) + "]) -> 0\n"
                        + "| \"below\" : ([" + item(3, false) + ", " + item(2, false) + "]) -> Bad\n"
                        + "| \"past\"  : ([" + item(4, true) + ", " + item(2, false) + "]) -> 0\n"
                        + "| \"short\" : ([" + item(1, true) + ", " + item(1, false)
                        + "]) -> Bad\n")));
    }

    /**
     * A remainder by a divisor below nought is the floored one the program computes, from the
     * divisor up to nought: the odd positions leave less than nought, and a remainder truncated
     * toward nought would leave them one and weigh every element alike.
     */
    @Test
    void aRemainderByADivisorBelowNoughtIsTheFlooredOne() {
        String human = report(model(
                "(i, c) -> if Int.floorMod(i, -2) < 0 then 3 * c else c", "xs") + """
                example check
                    | "at"    : ([4, 2], 0) -> 0
                    | "below" : ([3, 2], 0) -> Bad
                    | "past"  : ([2, 4], 0) -> 0
                    | "short" : ([4, 1], 0) -> Bad
                """);
        assertTrue(human.contains("the position mod -2 < 0"), human);
        everyPointIsTaken(human);
    }

    /** What chooses a number by position is a way this compiler writes no row for, and says so,
     *  rather than saying no row can be written. */
    @Test
    void aTotalChosenByPositionIsOneThisWritesNoRowForAndSaysSo() {
        String human = report(model(BRANCH, "xs"));
        assertTrue(human.contains("nothing could show a row can be written at the ON point"),
                human);
        assertTrue(human.contains("chosen by where they stand"), human);
        assertFalse(human.contains("no row can be written"), human);
    }

    /**
     * A row whose run stops before the comparison is no row at any point of it, whatever the total
     * its values read as.
     *
     * <p>What a total is read as is what a run comes to where it answers: {@code (c + 1) - 1} is
     * {@code c}, {@code 0 * (c + 1) + c} is {@code c}, and the first element of
     * {@code (if i == 0 then 0 else 1) * (c + 1)} is nought — while each run stops at {@code c + 1}
     * on the largest whole number. So the rows below read as a total at a point, and are the run's
     * to say they are not at it.
     */
    @Test
    void aRowWhoseRunStopsIsAtNoPointWhateverItsTotalReadsAs() {
        String max = String.valueOf(Long.MAX_VALUE);
        for (String[] spelled : new String[][] {
                {"(i, c) -> (c + 1) - 1", "[" + max + ", -" + max + "]"},
                {"(i, c) -> 0 * (c + 1) + c", "[" + max + ", -" + max + "]"},
                {"(i, c) -> (if i == 0 then 0 else 1) * (c + 1)", "[" + max + ", 10]"}}) {
            String human = report(model(spelled[0], "xs") + """
                    example check
                        | "stops" : (%s, 0) -> Bad
                    """.formatted(spelled[1]));
            assertTrue(human.contains("check stops") && human.contains("gave no answer"),
                    spelled[0] + "\n" + human);
            assertTrue(human.contains("obligations 0/4"), spelled[0] + "\n" + human);
            assertFalse(human.contains("only a row that does not hold is at"),
                    spelled[0] + "\n" + human);
        }
    }

    /** A document says the choice is by position, how the position is compared, and both
     *  answers, in the shape the schema says. */
    @Test
    void aDocumentSaysTheChoiceIsByPosition() {
        Compilation compilation = measured(model(BRANCH, "xs"));
        JsonNode document = JsonMapper.builder().build().readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        List<JsonNode> chosen = new ArrayList<>();
        document.findParents("kind").forEach(each -> {
            if ("position".equals(each.get("kind").asString())) {
                chosen.add(each);
            }
        });
        assertFalse(chosen.isEmpty(), () -> "the document writes the choice: " + document);
        for (JsonNode each : chosen) {
            assertEquals(2, each.get("divisor").asLong(), each::toString);
            assertEquals("==", each.get("relation").asString(), each::toString);
            assertEquals(0, each.get("against").asLong(), each::toString);
            assertEquals("form", each.get("whenHolds").get("kind").asString(), each::toString);
        }
        EveryObjectThisWritesIsShapedTheWayTheSchemaSaysTest.assertShapedLikeTheSchema(document);
    }

    private static Compilation measured(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static String report(String model) {
        Compilation compilation = measured(model);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
