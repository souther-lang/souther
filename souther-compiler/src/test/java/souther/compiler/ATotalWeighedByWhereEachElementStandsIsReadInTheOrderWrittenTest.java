package souther.compiler;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.partition.UndividedPosition;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.WhyAPlaceIsUndividedIsSaid;

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
 * <p>A weight that is arithmetic in the position, {@code (i + 2) * c}, is a number for each element
 * as well, and the total a form of the elements.
 *
 * <p>The elements may be handed from the last of them to the first, through {@code List.reverse}:
 * the position then counts from the far end, and an even number of them is the order written.
 * That is another total over the same elements, so it is another term, and a list turned round on
 * one branch only is two terms and not one.
 *
 * <p>And only there. A number that is not the position, a product of the position with itself or
 * of two numbers of the element: none is read by where the elements stand.
 *
 * <p>A model whose assertions read only the terms and what was left unread is measured without the
 * rows; one whose assertions read the rows, or what a search for one came to, is measured whole.
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
        assertFalse(UnreadBesideItsStops.in(human), human);
    }

    /** A test of the position written with the number first is the same test, and the same term. */
    @Test
    void aTestOfThePositionWrittenTheOtherWayRoundIsTheSameTerm() {
        String flipped = read(model("(i, c) -> if 0 == Int.floorMod(i, 2) then c else 3 * c",
                "xs"));
        assertTrue(flipped.contains(TERM), flipped);
    }

    /** A closure bound to a name is the closure. */
    @Test
    void aClosureBehindANameIsReadTheSame() {
        String human = read("""
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

    /** A choice whose answers are one answer turns on nothing, and is the total of the list: the
     *  number {@code List.sum(xs)} is, and no run of its elements beside it. */
    @Test
    void aChoiceThatAnswersAlikeIsNoChoice() {
        String human = read(model("(i, c) -> if Int.floorMod(i, 2) == 0 then c else c", "xs"));
        assertTrue(human.contains("List.sum(xs)"), human);
        assertFalse(human.contains("List.sum(xs[*])"), human);
        assertFalse(human.contains("the position"), human);
    }

    /** A total that does not turn on where the elements stand is read whatever order they are
     *  handed in. */
    @Test
    void aTotalNotTurningOnThePositionIsReadWhicheverEndTheElementsCameFrom() {
        String alike = read(model("(i, c) -> 3 * c", "List.reverse(xs)"));
        assertTrue(alike.contains("List.sum({3·the element itself + 0 | xs[*]})"), alike);
    }

    /** The same total over the list and over its reverse are two terms, not one, and the document
     *  writes them as two: which end the walk was handed the elements from is said of the run. */
    @Test
    void aTotalFromTheFarEndIsNotTheTotalFromTheNearEnd() {
        Compilation near = measured(model(BRANCH, "xs"));
        Compilation far = measuredWithoutTheRows(model(BRANCH, "List.reverse(xs)"));
        assertFalse(human(near).contains("from the far end"), human(near));
        assertTrue(human(far).contains("from the far end"), human(far));
        assertEquals(List.of("as_written"), handedIn(near));
        assertEquals(List.of("from_the_far_end"), handedIn(far));
    }

    /** Which end each run computed of the elements the document writes was handed them from, one
     *  word for each such run. */
    private static List<String> handedIn(Compilation compilation) {
        JsonNode document = JsonMapper.builder().build().readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        DocumentShape.assertShapedLikeTheSchema(document);
        List<String> out = new ArrayList<>();
        handedIn(document, out);
        return out.stream().distinct().toList();
    }

    private static void handedIn(JsonNode node, List<String> out) {
        if (node.isObject() && node.path("kind").asString("").equals("computed_occurrences")) {
            out.add(node.path("handed").asString("absent"));
        }
        node.forEach(child -> handedIn(child, out));
    }

    /** Turning the order round twice is the order written: the same term as the list itself, and
     *  three times is once. */
    @Test
    void theOrderTurnedRoundTwiceIsTheOrderWritten() {
        String twice = report(model(BRANCH, "List.reverse(List.reverse(xs))"));
        assertTrue(twice.contains(TERM), twice);
        assertFalse(twice.contains("from the far end"), twice);
        assertFalse(UnreadBesideItsStops.in(twice), twice);
        String thrice = read(model(BRANCH,
                "List.reverse(List.reverse(List.reverse(xs)))"));
        assertTrue(thrice.contains("from the far end"), thrice);
    }

    /** The position a weight reads is the one the elements are handed at, so a reverse of the
     *  weighed numbers afterwards leaves the total as it was. */
    @Test
    void aReverseAfterTheWeighingLeavesTheTotalAsItWas() {
        String after = read(model(BRANCH, "xs").replace("List.mapIndexed(" + BRANCH + ", xs)",
                "List.reverse(List.mapIndexed(" + BRANCH + ", xs))"));
        assertTrue(after.contains(TERM), after);
        assertFalse(after.contains("from the far end"), after);
    }

    /**
     * A total over what a helper behavior answers is not read by where the elements stand, turned
     * round before the helper weighs them or not: the helper's answer is a value made from the
     * list, and the caller does not see the position it was weighed at. That is how a helper is
     * read, and nothing about the order.
     */
    @Test
    void aTotalOverWhatAHelperWeighedIsNotReadWhetherOrNotItTurnsTheListRound() {
        for (String walked : List.of("ys", "List.reverse(ys)")) {
            String human = report("""
                    module p
                    data Bad
                    behavior check : (xs: List<Int>, n: Int) -> Int | Bad
                    behavior weigh : (ys: List<Int>) -> List<Int>
                    let weigh (ys) = List.mapIndexed(%s, %s)
                    let check (xs, n) = {
                        guard List.sum(weigh(xs)) >= 10 else Bad
                        0
                    }
                    """.formatted(BRANCH, walked));
            // Read as no weighing: the total a call works out places a row by what its run did.
            assertFalse(UnreadBesideItsStops.in(human), walked + "\n" + human);
            assertTrue(human.contains(WhyAPlaceIsUndividedIsSaid.of(
                            UndividedPosition.Reason.RULE_MEASURED_ON_ITS_RUNS)),
                    walked + "\n" + human);
            assertFalse(human.contains("the position"), walked + "\n" + human);
        }
    }

    /** A list that is the reverse on one branch and the list itself on the other is two totals,
     *  each counted from its own end, and never one counted from the end of the other. */
    @Test
    void aListReversedOnOneBranchOnlyIsReadAsTwoTotals() {
        String human = report("""
                module p
                data Bad
                behavior check : (xs: List<Int>, turned: Bool) -> Int | Bad
                let check (xs, turned) = {
                    let ys = if turned then List.reverse(xs) else xs
                    guard List.sum(List.mapIndexed(%s, ys)) >= 10 else Bad
                    0
                }
                example check
                    | "round, at"     : ([2, 4], true)  -> 0
                    | "round, below"  : ([2, 3], true)  -> Bad
                    | "round, past"   : ([4, 2], true)  -> 0
                    | "round, short"  : ([1, 4], true)  -> Bad
                    | "written, at"   : ([4, 2], false) -> 0
                    | "written, below": ([3, 2], false) -> Bad
                    | "written, past" : ([2, 4], false) -> 0
                    | "written, short": ([4, 1], false) -> Bad
                """.formatted(BRANCH));
        assertTrue(human.contains(TERM), human);
        assertTrue(human.contains(TERM.replace("xs[*]", "xs[*] from the far end")), human);
        assertFalse(UnreadBesideItsStops.in(human), human);
        assertTrue(human.contains("obligations 8/8"), human);
        assertFalse(human.contains("undecided whether a row is at"), human);
        assertFalse(human.contains("does not hold"), human);
    }

    /**
     * The model of the report that named this, a weight that changes past the sixth place: seven
     * elements, and the first of them is weighed three from the far end and two from the near one.
     */
    @Test
    void aWeightThatChangesPastTheSixthPlaceIsCountedFromTheFarEnd() {
        String human = report("""
                module probe.k7

                data Yes = { n: Int }
                data No = { n: Int }

                behavior verify : (xs: List<Int>) -> Yes | No
                    constructs Yes, No

                let verify (xs) =
                    if List.sum(List.mapIndexed((i, x) -> (if i <= 5 then 2 else 3) * x,
                            List.reverse(xs))) >= 5
                    then Yes { n = 0 } else No { n = 0 }

                example verify
                    | "at"    : ([1, 0, 0, 0, 0, 0, 1]) -> Yes { n = 0 }
                    | "below" : ([0, 0, 0, 0, 0, 0, 2]) -> No { n = 0 }
                    | "past"  : ([0, 0, 0, 0, 0, 0, 3]) -> Yes { n = 0 }
                    | "short" : ([1, 0, 0, 0, 0, 0, 0]) -> No { n = 0 }
                """);
        assertFalse(UnreadBesideItsStops.in(human), human);
        assertTrue(human.contains("obligations 4/4"), human);
        assertFalse(human.contains("undecided whether a row is at"), human);
        assertFalse(human.contains("does not hold"), human);
    }

    /** A whole number that is not the position is no position. */
    @Test
    void anotherNumberIsNoChoiceByThePosition() {
        String another = report(model(
                "(i, c) -> if Int.floorMod(n, 2) == 0 then c else 3 * c", "xs"));
        assertTrue(UnreadBesideItsStops.in(another), another);
        String notTheElement = report(model("(i, c) -> n * c", "xs"));
        assertTrue(UnreadBesideItsStops.in(notTheElement), notTheElement);
    }

    /**
     * Weighed two and three by position, {@code [4, 2]} is at fourteen, {@code [5, 1]} at thirteen,
     * {@code [2, 4]} at sixteen and {@code [3, 2]} at twelve — read without the order, or from the
     * end, none of them is at fourteen, so every point of the border is taken only on this reading.
     */
    @Test
    void aRowIsReadWithItsElementsWhereAWeightMadeOfThePositionPutsThem() {
        String guarded = """
                module p
                data Bad
                behavior check : (xs: List<Int>) -> Int | Bad
                let check (xs) = {
                    guard List.sum(List.mapIndexed((i, c) -> (i + 2) * c, xs)) >= 14 else Bad
                    0
                }
                example check
                    | "at"    : ([4, 2]) -> 0
                    | "below" : ([5, 1]) -> Bad
                    | "past"  : ([2, 4]) -> 0
                    | "short" : ([3, 2]) -> Bad
                """;
        String human = report(guarded);
        assertTrue(human.contains("obligations 4/4"), human);
        assertFalse(UnreadBesideItsStops.in(human), human);
    }

    /** The position by itself, with nothing of the element beside it, is read. */
    @Test
    void thePositionByItselfIsRead() {
        String human = report(model("(i, c) -> i", "xs"));
        assertTrue(human.contains("the position"), human);
        assertFalse(UnreadBesideItsStops.in(human), human);
    }

    /** Rows of no element and of one stand at the border of a total weighed by the position. */
    @Test
    void aRowOfNoElementAndOfOneIsHeldToTheSameWeights() {
        String human = report("""
                module p
                data Bad
                behavior check : (xs: List<Int>) -> Int | Bad
                let check (xs) = {
                    guard List.sum(List.mapIndexed((i, c) -> (i + 2) * c, xs)) >= 14 else Bad
                    0
                }
                example check
                    | "none" : ([]) -> Bad
                    | "one"  : ([7]) -> 0
                    | "less" : ([6]) -> Bad
                """);
        assertFalse(UnreadBesideItsStops.in(human), human);
        assertFalse(human.contains("gave no answer"), human);
    }

    /** No row is written by solving for a field through a weight made of the position, and the
     *  report says so rather than saying no row can be written. */
    @Test
    void aTotalWeighedByArithmeticInThePositionIsOneThisWritesNoRowForAndSaysSo() {
        String human = report(model("(i, c) -> (i + 2) * c", "xs"));
        assertTrue(human.contains("nothing could show a row can be written at the ON point"),
                human);
        assertFalse(human.contains("no row can be written"), human);
    }

    /** The total the report says a rule is about: the part between the backquotes after "about". */
    private static String totalOf(String human) {
        int from = human.indexOf("about `List.sum(");
        assertTrue(from >= 0, human);
        int start = from + "about `".length();
        return human.substring(start, human.indexOf('`', start));
    }

    private static String ofPairs(String closure) {
        return read("""
                module p
                data Pair = { p: Int, q: Int }
                data Bad
                behavior check : (xs: List<Pair>) -> Int | Bad
                let check (xs) = {
                    guard List.sum(List.mapIndexed(%s, xs)) >= 10 else Bad
                    0
                }
                """.formatted(closure));
    }

    /**
     * A weight made of the position is one number however it is written: the position added to a
     * choice of the position, on either side of the element it weighs, and a choice between two
     * weights each made of the position, are the choice with the position in each of its answers,
     * so the same term.
     */
    @Test
    void aWeightIsTheSameTermHoweverItsPositionAndItsChoiceAreAdded() {
        String inside = totalOf(read(model(
                "(i, c) -> (if i <= 5 then i + 2 else i - 4) * c", "xs")));
        for (String closure : List.of("(i, c) -> (i + (if i <= 5 then 2 else -4)) * c",
                "(i, c) -> c * (i + (if i <= 5 then 2 else -4))",
                "(i, c) -> if i <= 5 then (i + 2) * c else (i - 4) * c")) {
            String human = report(model(closure, "xs"));
            assertFalse(UnreadBesideItsStops.in(human), closure + "\n" + human);
            assertEquals(inside, totalOf(human), closure);
        }
    }

    /** Numbers made of the position and of the element are added as forms, so one number is one
     *  term whether the position multiplies each field, on either side, or their sum. */
    @Test
    void thePositionTimesEachFieldIsTheSameTermAsTheSumOfThem() {
        String together = totalOf(ofPairs("(i, c) -> i * (c.p + c.q)"));
        assertEquals(together, totalOf(ofPairs("(i, c) -> c.p * i + i * c.q")));
    }

    /** The case the issue reports, whose total is read through a remainder. */
    @Test
    void aTotalWeighedByTheIndexIsReadThroughARemainder() {
        String human = report("""
                module probe.f5

                data Yes = { n: Int }
                data No = { n: Int }

                behavior verify : (xs: List<Int>) -> Yes | No
                    constructs Yes, No

                let verify (xs) =
                    if Int.floorMod(List.sum(List.mapIndexed((i, c) -> (i + 2) * c, xs)), 11) <= 1 then Yes { n = 0 } else No { n = 0 }
                """);
        assertFalse(UnreadBesideItsStops.in(human), human);
        assertTrue(human.contains("the position"), human);
    }

    /** A product of two numbers of the element stays a product, whatever the position. */
    @Test
    void aProductOfTwoNumbersOfTheElementIsStillNotRead() {
        String human = report("""
                module p
                data Pair = { p: Int, q: Int }
                data Bad
                behavior check : (xs: List<Pair>) -> Int | Bad
                let check (xs) = {
                    guard List.sum(List.mapIndexed((i, c) -> i * c.p * c.q, xs)) >= 10 else Bad
                    0
                }
                """);
        assertTrue(UnreadBesideItsStops.in(human), human);
    }

    /** A weight that is the position squared is no form of the elements. */
    @Test
    void thePositionTimesItselfIsStillNotRead() {
        String human = report(model("(i, c) -> i * i * c", "xs"));
        assertTrue(UnreadBesideItsStops.in(human), human);
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
     * toward nought would leave them one and weigh every element alike. Weighed one and three by
     * position, {@code [4, 2]} is at ten and {@code [3, 2]} at nine, {@code [2, 4]} past the line
     * and {@code [4, 1]} short of it, and read without the order none of them is at ten.
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
        assertTrue(human.contains("by where they stand"), human);
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
            String human = report(List.of("E1905"), model(spelled[0], "xs") + """
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

    /** Each model measured once for the class: several tests ask one model, and only read it. */
    private static final ACompiledModel.Shared SHARED = new ACompiledModel.Shared();

    /** Given back when the class is done with them: a fork keeps its JVM, so what is held
     *  statically is held for every class after this one. */
    @AfterAll
    static void released() {
        SHARED.release();
    }

    /** Held apart from the same source measured whole, since the key is all the holder asks. */
    private static final String WITHOUT_THE_ROWS = "without the rows\n";

    private static Compilation measure(String model, Adequacy.Asked asked) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(asked);
        return compilation;
    }

    private static Compilation measured(String model) {
        return SHARED.compiles(model, () -> measure(model, Adequacy.Asked.fullReport()));
    }

    /** The model with what it says of itself and nothing measured of the rows. */
    private static Compilation measuredWithoutTheRows(String model) {
        return SHARED.compiles(WITHOUT_THE_ROWS + model,
                () -> measure(model, new Adequacy.Asked(Adequacy.Level.OFF, false)));
    }

    private static String human(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String report(String model) {
        return human(measured(model));
    }

    /** The report of a model measured without the rows. */
    private static String read(String model) {
        return human(measuredWithoutTheRows(model));
    }

    /** The report of a model the compiler is meant to refuse with {@code refused}. */
    private static String report(List<String> refused, String model) {
        return human(SHARED.refusedWith(refused, model,
                () -> measure(model, Adequacy.Asked.fullReport())));
    }
}
