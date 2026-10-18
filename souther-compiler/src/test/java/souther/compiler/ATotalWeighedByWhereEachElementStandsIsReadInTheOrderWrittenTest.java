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
