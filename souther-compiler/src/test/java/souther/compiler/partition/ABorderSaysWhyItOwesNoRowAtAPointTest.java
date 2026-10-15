package souther.compiler.partition;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import org.junit.jupiter.api.Test;

import souther.compiler.ARuleNoReadingTakesIn;
import souther.compiler.numeric.Towards;
import souther.compiler.query.Adequacy;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A border owes a row at four points, and where it owes none it says which of three things settled
 * that.
 *
 * <p>Every one of these used to be a coverage item that was never built. The obligation was left out
 * of a list, and all of them reached a reader as the same thing — one fewer entry — so a reader
 * counting the four items the technique asks for found this compiler short and was never told which
 * of them had happened. Two of the three are not shortfalls at all: the rules refusing the point is
 * the model having discharged it, and a carrier naming no value one step over is an item that cannot
 * exist.
 *
 * <p>Each reason is measured against a model that differs from it in one thing and owes the row. An
 * expectation on one model alone holds against a reader that answers "not owed" everywhere, which is
 * exactly what leaving the entry out amounted to.
 */
class ABorderSaysWhyItOwesNoRowAtAPointTest {

    /** A newtype bounded by {@code rule}, held in a record, with a guard at {@code guard} on it. */
    private static String model(String carrier, String rule, String guard, String row) {
        return """
                module example.owed

                data A = %s
                    invariant bound = value %s

                data H = { a: A }

                data Ok
                data No
                data Verdict = Ok | No

                behavior take : (h: H) -> Verdict
                let take (h) = { guard h.a.value %s else Ok
                    No }

                example take
                    | "one" : (H { a = A(%s) }) -> No
                """.formatted(carrier, rule, guard, row);
    }

    /**
     * A bound owes nothing outside itself, and a guard at the same value owes the step over.
     *
     * <p>The pair is the measurement. Both borders are on one position and one is at the very value
     * the other is, so what differs between the two answers is which rule drew the line — which is
     * the whole of what decides whether there is a far side at all.
     */
    @Test
    void theRulesRefuseThePointsOutsideABound() {
        Map<String, BorderAssessment> borders = bordersOf(model("Int", ">= 0", "<= 100", "50"));

        BorderAssessment bound = borders.get("h.a = 0");
        assertNotNull(bound, borders.keySet().toString());
        assertEquals(new souther.compiler.query.ItemAssessment.NotOwed(
                        NotOwedReason.NO_VALUE_CAN_STAND_THERE), bound.at(PointRole.OFF));
        assertEquals(new souther.compiler.query.ItemAssessment.NotOwed(
                        NotOwedReason.NO_VALUE_CAN_STAND_THERE), bound.at(PointRole.OUT));

        BorderAssessment guard = borders.get("h.a = 100");
        assertNotNull(guard, borders.keySet().toString());
        assertEquals("101", guard.against(PointRole.OFF),
                "a guard leaves values either side, so the step over is a row somebody is owed");
        assertEquals("in 101 < h.a",
                guard.operator(PointRole.OUT) + " " + guard.against(PointRole.OUT));
    }

    /**
     * A carrier with no next value names no point one step over, and one that has a next value does.
     *
     * <p>Told apart from the reason above rather than folded into it. This one is a limit of what
     * the language can write down; that one is the model refusing the value. A reader handed the
     * second about a point the rules refuse would go looking for a missing conversion.
     */
    @Test
    void aCarrierWithNoNextValueNamesNoPointBesideTheLine() {
        assertEquals("101",
                bordersOf(model("Int", ">= 0", "<= 100", "50")).get("h.a = 100")
                        .against(PointRole.OFF),
                "a whole number has a next one");
        assertEquals(new souther.compiler.query.ItemAssessment.NotOwed(
                        NotOwedReason.THE_CARRIER_NAMES_NO_NEIGHBOUR),
                bordersOf(model("Decimal", ">= 0m", "<= 100m", "50m")).get("h.a = 100")
                        .at(PointRole.OFF),
                "and a decimal has none, so the point one step over is not named at all");
    }

    /**
     * A position whose rules name its values refuses every point that is none of them, though the
     * order has a value there and the range runs past it.
     *
     * <p>Against the same rules naming the value as well, which owe the row: what refuses the point
     * is that the value is not named, and not the shape of the rule.
     */
    @Test
    void theRulesNamingTheValuesRefuseAPointThatIsNoneOfThem() {
        String named = " == 1 || value == 3 || value == 7";
        assertEquals(NOT_OWED, bordersOf(model("Int", named, "< 3", "1")).get("h.a = 3")
                .at(PointRole.ON), "two is no value of the three");
        assertEquals("2", bordersOf(model("Int", " == 1 || value == 2 || value == 3 || value == 7",
                "< 3", "1")).get("h.a = 3").against(PointRole.ON), "and is one of the four");
        // A value left out of a run is refused the same way, by the one value left out.
        assertEquals(NOT_OWED, bordersOf(model("Int", " >= 1 && value <= 5 && value /= 2", "< 3",
                "1")).get("h.a = 3").at(PointRole.ON));
    }

    /**
     * The same of a run: one between two lines that holds none of the values named is refused, and
     * one holding a single one of them is owed a row at it.
     *
     * <p>{@code "a"} and {@code "b"} have {@code "a0"} and {@code "a1"} between them on the order of
     * the strings, and the run between those two holds no value of a position holding one of the
     * two. Of a position holding {@code "a05"} besides, it holds that one.
     *
     * <p>And of every place the position stands: an element of a list holds what the element's
     * rules name, and a rule nothing reads beside the ones that name the values may refuse some of
     * them and admits no other — so what it leaves is still none of the run.
     */
    @Test
    void theRulesNamingTheValuesRefuseARunHoldingNoneOfThem() {
        for (String type : List.of("Code", "List<Code>", "Loose")) {
            Map<String, BorderAssessment> borders = bordersOf(twoLines(type,
                    "value == \"a\" || value == \"b\""));
            assertEquals(NOT_OWED, borders.get(on(type) + " = a0").at(PointRole.OUT), type);
            assertEquals(NOT_OWED, borders.get(on(type) + " = a1").at(PointRole.IN), type);
            assertEquals(NOT_OWED, borders.get(on(type) + " = a0").at(PointRole.OFF), type);
            assertEquals(NOT_OWED, borders.get(on(type) + " = a1").at(PointRole.OFF), type);
        }
        Map<String, BorderAssessment> held = bordersOf(twoLines("Code",
                "value == \"a\" || value == \"a05\" || value == \"b\""));
        assertTrue(held.get("c = a0").at(PointRole.OUT) instanceof ItemAssessment.Owed,
                () -> held.get("c = a0").toString());
        assertTrue(held.get("c = a1").at(PointRole.IN) instanceof ItemAssessment.Owed,
                () -> held.get("c = a1").toString());
    }

    /**
     * A rule naming a value the declarations refuse draws no line, the same as one naming a value
     * outside the range: no row stands at it, so it parts the position's values nowhere.
     *
     * <p>Of a string held to a few values, of the element of a list of them, and of a number held
     * to a class of whole numbers. Against the same rule over a position that holds the value,
     * which draws it.
     */
    @Test
    void aValueTheDeclarationsRefuseDrawsNoLine() {
        String code = "value == \"a\" || value == \"b\"";
        assertFalse(bordersOf(naming("Code", "String", code, "c.value == \"a0\""))
                .containsKey("c = a0"));
        assertFalse(bordersOf(naming("List<Code>", "String", code,
                "List.any(x -> x.value == \"a0\", c)")).containsKey("c[*] = a0"));
        assertFalse(bordersOf(naming("Code", "Int",
                "value >= 0 && value <= 10000 && Int.floorMod(value, 1000) == 0",
                "c.value == 1500")).containsKey("c = 1500"));
        assertTrue(bordersOf(naming("Code", "String",
                        "value == \"a\" || value == \"a0\" || value == \"b\"", "c.value == \"a0\""))
                .containsKey("c = a0"));
    }

    /** A behavior over {@code type}, built of a {@code Code} on {@code carrier} held by
     *  {@code rule}, deciding on {@code condition}. */
    private static String naming(String type, String carrier, String rule, String condition) {
        return """
                module example.owed

                data Code = %s
                    invariant %s

                data Ok
                data No
                data Verdict = Ok | No

                behavior take : (c: %s) -> Verdict
                let take (c) = if %s then No else Ok
                """.formatted(carrier, rule, type, condition);
    }

    /**
     * What the rules name are values of the position and not of a number taken of it.
     *
     * <p>A string held to {@code "a"} or {@code "b"} is one character long, and a point at a length
     * of one is owed a row. Put to the set of strings, a length of one is no string the set names
     * and the point would be refused.
     */
    @Test
    void theValuesNamedSayNothingOfANumberTakenOfThem() {
        Map<String, BorderAssessment> borders = bordersOf("""
                module example.owed

                data Code = String
                    invariant value == "a" || value == "b"

                data Ok
                data No
                data Verdict = Ok | No

                behavior take : (c: Code) -> Verdict
                let take (c) = if String.length(c.value) < 2 then No else Ok

                example take
                    | "one" : (Code("a")) -> No
                """);
        BorderAssessment length = borders.get("String.length(c) = 2");
        assertNotNull(length, borders.keySet().toString());
        assertEquals("1", length.against(PointRole.ON));
    }

    /**
     * A number taken of a position whose rules name its values is held to the numbers those values
     * come to, and a point or a run holding none of them is refused as one of the value itself is.
     *
     * <p>{@code "a"} and {@code "b"} are both one long, so a guard at one owes nothing at nought
     * and nothing past one, and owes the row at one.
     */
    @Test
    void aNumberTakenOfTheValuesNamedIsHeldToTheNumbersTheyComeTo() {
        BorderAssessment line = lineOf(naming("Code", "String", "value == \"a\" || value == \"b\"",
                "String.length(c.value) < 1"), "String.length(c) = 0");
        assertEquals(List.of("ON: NO_VALUE_CAN_STAND_THERE", "OFF = 1: owed",
                        "IN: NO_VALUE_CAN_STAND_THERE", "OUT: NO_VALUE_CAN_STAND_THERE"),
                owedAt(line), "no value named is empty, and none is longer than one");
    }

    /** Each point of {@code line}, with what a row there is asked and whether one is owed, or why
     *  none is. */
    private static List<String> owedAt(BorderAssessment line) {
        List<String> said = new ArrayList<>();
        for (BorderAssessment.Point point : line.points()) {
            said.add(point.role() + (point.asked() == null ? "" : " " + point.asked()) + ": "
                    + switch (point.item()) {
                case ItemAssessment.Owed _ -> "owed";
                case ItemAssessment.NotOwed not -> not.reason().name();
                case ItemAssessment.NotWorkedOut not -> "not worked out: " + not.why();
            });
        }
        return said;
    }

    /**
     * The numbers the values come to, and not the run between the least and the greatest of them.
     *
     * <p>{@code "a"} and {@code "bbb"} are one and three long and nothing between, so a point at two
     * is refused while the runs either side of it hold one of the two.
     */
    @Test
    void theNumbersTheValuesComeToLeaveTheGapsBetweenThem() {
        String named = "value == \"a\" || value == \"bbb\"";
        BorderAssessment underThree = lineOf(naming("Code", "String", named,
                "String.length(c.value) < 3"), "String.length(c) = 3");
        assertEquals(NOT_OWED, underThree.at(PointRole.ON), "nothing named is two long");
        assertTrue(underThree.at(PointRole.OFF) instanceof ItemAssessment.Owed,
                underThree::toString);

        BorderAssessment underTwo = lineOf(naming("Code", "String", named,
                "String.length(c.value) < 2"), "String.length(c) = 2");
        assertTrue(underTwo.at(PointRole.ON) instanceof ItemAssessment.Owed, underTwo::toString);
        assertEquals(NOT_OWED, underTwo.at(PointRole.OFF), "nothing named is two long");
        assertTrue(underTwo.at(PointRole.OUT) instanceof ItemAssessment.Owed,
                () -> "three is past two: " + underTwo);
    }

    /**
     * A number the values named come to is offered a row holding one of them.
     *
     * <p>Three is a length {@code "bbb"} has, and a string of three nobody named is one the rules
     * refuse. Offered that string, the point would come back as one every value tried at was
     * refused.
     *
     * <p>Whichever rules name the values: the string's own type, or the record holding it as a
     * field, whose rules the type of the field knows nothing of.
     */
    @Test
    void aNumberTheValuesNamedComeToIsOfferedOneOfThem() {
        assertEquals(List.of("Code(\"bbb\")"), offeredAt(naming("Code", "String",
                        "value == \"a\" || value == \"bbb\"", "String.length(c.value) < 3"),
                "String.length(c) = 3", PointRole.OFF));
        assertEquals(List.of("Request { code = \"bbb\" }"), offeredAt("""
                        module example.owed

                        data Request = { code: String }
                            invariant code == "a" || code == "bbb"

                        data Ok
                        data No
                        data Verdict = Ok | No

                        behavior take : (r: Request) -> Verdict
                        let take (r) = if String.length(r.code) < 3 then No else Ok
                        """, "String.length(r.code) = 3", PointRole.OFF));
    }

    /**
     * A run of a number taken of the position is offered a row at a number one of the values comes
     * to, however far into the run that is.
     *
     * <p>Forty is the only length past five any value named has. Walked from five upward over every
     * length, what a walk may try runs out long before forty, and the run came back as one nothing
     * could build a value for.
     */
    @Test
    void aRunOfANumberTakenOfTheValuesNamedIsOfferedTheNumberOneOfThemComesTo() {
        String far = "b".repeat(40);
        assertEquals(List.of("Code(\"" + far + "\")"), offeredAt(naming("Code", "String",
                        "value == \"a\" || value == \"" + far + "\"", "String.length(c.value) < 5"),
                "String.length(c) = 5", PointRole.OUT));
    }

    /**
     * The same of a remainder: two is left by eight and not by four, so the row offered at two
     * holds eight rather than the first whole number that leaves two.
     */
    @Test
    void aRemainderTheValuesNamedLeaveIsOfferedTheOneThatLeavesIt() {
        assertEquals(List.of("Code(8)"), offeredAt(naming("Code", "Int",
                        "value == 4 || value == 8", "Int.floorMod(c.value, 3) < 2"),
                "Int.floorMod(c, 3) = 2", PointRole.OFF));
    }

    /**
     * A set that is not finitely many values holds a number taken of it to nothing, so the points
     * the rules leave values at are owed as they are of any string.
     *
     * <p>Every string but {@code "a"} includes the empty one, and a pattern of letters includes
     * strings one long.
     */
    @Test
    void aSetThatIsNotFinitelyManyValuesRefusesNoPointOfANumberTakenOfIt() {
        assertTrue(lineOf(naming("Code", "String", "value /= \"a\"",
                        "String.length(c.value) < 1"), "String.length(c) = 0")
                .at(PointRole.ON) instanceof ItemAssessment.Owed);
        assertTrue(lineOf(naming("Code", "String", "String.matches(\"[a-z]+\", value)",
                        "String.length(c.value) < 2"), "String.length(c) = 2")
                .at(PointRole.ON) instanceof ItemAssessment.Owed);
    }

    /** Each row offered at {@code role} of the border of {@code model} at {@code label}, as its
     *  inputs are written. */
    private static List<String> offeredAt(String model, String label, PointRole role) {
        Compilation compiled = compiled(model);
        BorderAssessment line = Adequacy.searchedBoundariesOf(compiled.db(), "example.owed")
                .values().stream().flatMap(List::stream)
                .filter(each -> each.label().equals(label)).findFirst()
                .orElseThrow(() -> new AssertionError("no border at " + label));
        List<String> offered = new ArrayList<>();
        for (ItemAssessment.Attempt attempt : line.owedAt(role).searches().each()) {
            if (attempt instanceof ItemAssessment.Attempt.Built built) {
                offered.add(String.join(", ",
                        built.row().inputs().stream().map(FixtureTemplate::text).toList()));
            }
        }
        return offered;
    }

    /**
     * A value named empty is nought long, and a value outside the basic plane is one long: the
     * number is the one the term reads of the value, counted in code points.
     */
    @Test
    void theNumbersAreTheOnesTheTermReadsOfEachValue() {
        BorderAssessment empty = lineOf(naming("Code", "String", "value == \"\" || value == \"a\"",
                "String.length(c.value) < 1"), "String.length(c) = 0");
        assertTrue(empty.at(PointRole.ON) instanceof ItemAssessment.Owed, empty::toString);
        assertEquals(NOT_OWED, empty.at(PointRole.OUT), "and nothing named is longer than one");

        BorderAssessment astral = lineOf(naming("Code", "String", "value == \"😀\"",
                "String.length(c.value) < 2"), "String.length(c) = 2");
        assertTrue(astral.at(PointRole.ON) instanceof ItemAssessment.Owed, astral::toString);
        assertEquals(NOT_OWED, astral.at(PointRole.OFF), "one code point is one long");
    }

    /**
     * Of any number taken of the position and not of a length alone: a remainder is read of each
     * value with what it was given beside it.
     *
     * <p>One and four leave one by three, so a guard at one owes nothing at nought or at two.
     */
    @Test
    void aRemainderOfTheValuesNamedIsHeldToTheRemaindersTheyLeave() {
        Map<String, BorderAssessment> borders = bordersOf(naming("Code", "Int",
                "value == 1 || value == 4", "Int.floorMod(c.value, 3) < 1"));
        BorderAssessment line = borders.values().stream()
                .filter(each -> each.label().startsWith("Int.floorMod")).findFirst()
                .orElseThrow(() -> new AssertionError(borders.keySet().toString()));
        assertEquals(NOT_OWED, line.at(PointRole.ON), "neither leaves nought");
        assertTrue(line.at(PointRole.OFF) instanceof ItemAssessment.Owed, line::toString);
        assertEquals(NOT_OWED, line.at(PointRole.OUT), "nor two");
    }

    /**
     * And of a count of some of the code points of the string, which no operation answers.
     *
     * <p>{@code "a"} and {@code " b "} each hold one code point that is not whitespace, so what is
     * left of either once trimmed is never empty and never longer than one.
     */
    @Test
    void aCountOfTheCodePointsOfTheValuesNamedIsHeldToTheCountsTheyHold() {
        Map<String, BorderAssessment> borders = bordersOf(naming("Code", "String",
                "value == \"a\" || value == \" b \"", "String.length(String.trim(c.value)) < 1"));
        BorderAssessment line = borders.values().stream()
                .filter(each -> each.label().startsWith("#(")).findFirst()
                .orElseThrow(() -> new AssertionError(borders.keySet().toString()));
        assertEquals(List.of("ON: NO_VALUE_CAN_STAND_THERE", "OFF = 1: owed",
                        "IN: NO_VALUE_CAN_STAND_THERE", "OUT: NO_VALUE_CAN_STAND_THERE"),
                owedAt(line));
    }

    /** The border of {@code model} at {@code label}. */
    private static BorderAssessment lineOf(String model, String label) {
        Map<String, BorderAssessment> borders = bordersOf(model);
        BorderAssessment line = borders.get(label);
        assertNotNull(line, borders.keySet().toString());
        return line;
    }

    private static final ItemAssessment.NotOwed NOT_OWED =
            new ItemAssessment.NotOwed(NotOwedReason.NO_VALUE_CAN_STAND_THERE);

    /** Where the lines of {@link #twoLines} stand: the position, or each element of it. */
    private static String on(String type) {
        return type.startsWith("List") ? "c[*]" : "c";
    }

    /**
     * Lines at {@code "a0"} and {@code "a1"} on a position of {@code type}, a string or a list of
     * strings held to what {@code named} names.
     */
    private static String twoLines(String type, String named) {
        String below = type.startsWith("List") ? "List.any(x -> x.value < \"%s\", c)"
                : "c.value < \"%s\"";
        String read = below.formatted("a0") + " then Ok else if " + below.formatted("a1");
        return """
                module example.owed

                data Code = String
                    invariant %s

                data Loose = String
                    invariant (%s) && %s

                data Ok
                data No
                data Verdict = Ok | No

                behavior take : (c: %s) -> Verdict
                let take (c) = if %s then No else Ok
                """.formatted(named, named, ARuleNoReadingTakesIn.about("value"), type, read);
    }

    /**
     * A rule that names a value owes a row at it and at the nearest value on each side of it.
     *
     * <p>Both neighbours are in the class such a rule keeps out. What it distinguishes is the one
     * value from every other one, so each of the two crosses the line and each is a point of its
     * own — and a row at one of them says nothing about the other, which is what makes them two.
     *
     * <p>Against an ordering at the same value, where one neighbour crosses and the other does not.
     * That is the whole of the difference between the two shapes of line: the value below
     * {@code <= 100} is in the partition the border bounds, and a row there answers for the point
     * away from the line rather than for a point against it.
     *
     * <p>Both spellings of the naming rule, because the roles reverse and the values do not.
     * {@code == 100} is met at the value and not beside it and {@code /= 100} is the other way
     * about, and the three places a row is asked for are the same three.
     */
    @Test
    void aRuleThatNamesAValueOwesAPointOnEachSideOfIt() {
        assertEquals(java.util.Set.of("h.a = 99", "h.a = 100", "h.a = 101"),
                atALevel(model("Int", ">= 0", "== 100", "50")),
                "the value the rule names, and the nearest value on each side of it");

        assertEquals(java.util.Set.of("h.a = 99", "h.a = 100", "h.a = 101"),
                atALevel(model("Int", ">= 0", "/= 100", "50")),
                "the same three places, whichever of the two classes the rule selects");

        assertEquals(java.util.Set.of("h.a = 100", "h.a = 101"),
                atALevel(model("Int", ">= 0", "<= 100", "50")),
                "an ordering leaves the value below its line in the partition it bounds, so that"
                        + " one is no point against the line");
    }

    /**
     * A rule that names a value draws a line exactly where the rules leave that value.
     *
     * <p>Such a rule parts the value it names from every other one, so what says whether it divides
     * anything is whether the position holds the value — and not whether it holds anything one step
     * either side of it. A rule naming a value the rules refuse divides nothing: every value left
     * is in one class, and there is no line for a row to be beside.
     *
     * <p>Every spelling at every place, because the question is about the value and the two
     * operators and the three places must not be able to answer it differently. A rule satisfied at
     * the value and one refusing it name the same value, and a value at the end of the range is as
     * much a value the rules leave as one in the middle.
     */
    @Test
    void aRuleThatNamesAValueDrawsWhereverTheRulesLeaveThatValue() {
        assertEquals(List.of("/= 0 -> [h.a = 0]", "== 0 -> [h.a = 0]",
                        "/= 50 -> [h.a = 50]", "== 50 -> [h.a = 50]",
                        "/= 100 -> [h.a = 100]", "== 100 -> [h.a = 100]",
                        "/= 200 -> []", "== 200 -> []"),
                linesDrawnBy("/= 0", "== 0", "/= 50", "== 50", "/= 100", "== 100",
                        "/= 200", "== 200"),
                "a value the rules leave is a line wherever in the range it falls, and a value they"
                        + " refuse is no line at all");
    }

    /**
     * At an end of the range one of the two values beside the line is a value the rules leave and
     * the other is not, and the two are answered apart.
     *
     * <p>The edge case the whole of this identity is for. A rule naming the value the rules stop at
     * has a point on each side of it, and only one of them is a value a row can hold — so a border
     * that had one place for the two would have to answer for both at once, and whichever answer it
     * gave would be wrong about the other.
     *
     * <p>Both operators against one table, because the place and what the rules leave there are the
     * same for the two and only the role turns over. That is the whole of what putting the identity
     * in the place and the classification in the rule buys, said as one measurement.
     */
    @Test
    void atAnEndOfTheRangeTheTwoValuesBesideTheLineAreAnsweredApart() {
        assertEquals(List.of(
                        "== 100: beside below = 99 (OFF), beside above = NO_VALUE_CAN_STAND_THERE",
                        "/= 100: beside below = 99 (ON), beside above = NO_VALUE_CAN_STAND_THERE",
                        "== 0: beside below = NO_VALUE_CAN_STAND_THERE, beside above = 1 (OFF)",
                        "/= 0: beside below = NO_VALUE_CAN_STAND_THERE, beside above = 1 (ON)",
                        "== 50: beside below = 49 (OFF), beside above = 51 (OFF)",
                        "/= 50: beside below = 49 (ON), beside above = 51 (ON)"),
                besideTheLineOf("== 100", "/= 100", "== 0", "/= 0", "== 50", "/= 50"),
                "the value beside the line on each side is asked for on its own, and the rules"
                        + " refusing one of them says nothing about the other");
    }

    /**
     * A rule that names a value has no point in one of the four roles, and says which and why.
     *
     * <p>The class its own value is in holds that value and nothing else, so there is nowhere in it
     * away from the line: {@code == 50} has no {@code IN} point and {@code /= 50} no {@code OUT}
     * one. That is not a point the rules refuse — it is a word the technique has for something such
     * a line does not have — and a reader told nothing about it cannot tell the two apart from the
     * four words being four.
     *
     * <p>An order beside them, where every word is played and none of this arises.
     */
    @Test
    void aRuleThatNamesAValueHasNoPointInOneOfTheFourRoles() {
        assertEquals(List.of("ON x1", "OFF x2", "IN none", "OUT x2"),
                rolesOf(onlyLineOf(model("Int", ">= 0 && value <= 100", "== 50", "50"))),
                "what a rule naming a value keeps out is two runs and two values, and what it keeps"
                        + " is the value alone");
        assertEquals(List.of("ON x2", "OFF x1", "IN x2", "OUT none"),
                rolesOf(onlyLineOf(model("Int", ">= 0 && value <= 100", "/= 50", "50"))),
                "and the same places one class over");
        assertEquals(List.of("ON x1", "OFF x1", "IN x1", "OUT x1"),
                rolesOf(onlyLineOf(model("Int", ">= 0 && value <= 100", "<= 50", "50"))),
                "an order plays every one of the four once");

        assertEquals(RoleAnswer.Reason.THE_CLASS_AT_THE_LINE_HOLDS_ONE_VALUE,
                ((RoleAnswer.NoPoint) onlyLineOf(model("Int", ">= 0 && value <= 100", "== 50", "50"))
                        .inEachRole().get(PointRole.IN)).why(),
                "and what settles the absence is the class at the line holding one value");
    }

    /** How many points of one line play each of the four roles, every role answered. */
    private static List<String> rolesOf(Border line) {
        List<String> said = new ArrayList<>();
        line.inEachRole().forEach((role, answer) -> said.add(role + " " + switch (answer) {
            case RoleAnswer.Played played -> "x" + played.at().size();
            case RoleAnswer.NoPoint _ -> "none";
        }));
        return said;
    }

    /** What each guard's line asks at the value beside it on each side, over a position the rules
     *  leave {@code 0..100}. */
    private static List<String> besideTheLineOf(String... guards) {
        List<String> said = new ArrayList<>();
        for (String guard : guards) {
            Border line = onlyLineOf(model("Int", ">= 0 && value <= 100", guard, "50"));
            said.add(guard + ": " + beside(line, Towards.BELOW)
                    + ", " + beside(line, Towards.ABOVE));
        }
        return said;
    }

    /** What one line asks at the value beside it on one side, with which of the four that point is
     *  where a row is owed there. */
    private static String beside(Border line, Towards side) {
        DomainPoint at = new DomainPoint.BesideTheLine(side);
        String where = "beside " + (side == Towards.BELOW ? "below" : "above") + " = ";
        return switch (line.answer(at)) {
            case PointAnswer.NotOwed not -> where + not.reason();
            case PointAnswer.NotWorkedOut not -> where + "not worked out: " + not.why();
            case PointAnswer.AtLine _ -> where + line.against(at) + " (" + line.roleOf(at) + ")";
            case PointAnswer.InRegion in -> where + in;
        };
    }

    /** The one line a guard of this model draws, without the two the bounds of the range draw. */
    private static Border onlyLineOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        List<Border> drawn = Adequacy.boundariesOf(compilation.db(), "example.owed").values()
                .stream().flatMap(List::stream).map(BorderAssessment::border)
                .filter(each -> !(each.origin() instanceof LineOrigin.InvariantOrigin)).toList();
        assertEquals(1, drawn.size(), () -> "this model draws one line of its own: " + drawn);
        return drawn.get(0);
    }

    /** The lines each guard draws over a position the rules leave {@code 0..100}, without the two
     *  the bounds of that range draw themselves. */
    private static List<String> linesDrawnBy(String... guards) {
        List<String> drawn = new java.util.ArrayList<>();
        for (String guard : guards) {
            Compilation compilation = Compilation.ofSource(
                    model("Int", ">= 0 && value <= 100", guard, "50"), "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            drawn.add(guard + " -> " + Adequacy.boundariesOf(compilation.db(), "example.owed")
                    .values().stream().flatMap(List::stream)
                    .filter(each -> !(each.origin() instanceof LineOrigin.InvariantOrigin))
                    .map(BorderAssessment::label).toList());
        }
        return drawn;
    }

    /** Every value of the quantity this model's line asks a row at, as a report writes it. Asked of
     *  the answers themselves rather than of the four roles, because what is being counted is how
     *  many places the line asks for and a role is what one of them is. */
    private static java.util.Set<String> atALevel(String model) {
        BorderAssessment line = bordersOf(model).get("h.a = 100");
        assertNotNull(line, bordersOf(model).keySet().toString());
        return line.border().answers().values().stream()
                .map(PointAnswer::criterion)
                .filter(each -> each instanceof Criterion.AtTheLevel)
                .map(line.border()::label)
                .collect(java.util.stream.Collectors.toCollection(java.util.LinkedHashSet::new));
    }

    /**
     * A row on the line is not a row at a point past it, whatever the search had to start from.
     *
     * <p>An order with no numbers has one level — where the two are equal — and a point past it is a
     * run the level is not in. Read as a level the item accepts, a pair standing equal came back for
     * a point that lies strictly past them.
     *
     * <p><b>Of every row offered at such a point, and not of one pair.</b> Which pair a search
     * happens to compose is its own answer and moves when it learns to reach further; that a row
     * offered for a strict side stands on the line is wrong whichever pair it is. Written as one
     * literal, the check went on passing the day the search composed a different equal pair.
     *
     * <p>And nothing here says a row has to be found. Whether the search reaches one is a question
     * about how far it can look, and a point it reaches none at is reported as such — so what is
     * counted below is the points examined, which is what keeps this from passing because there was
     * nothing to look at.
     */
    @Test
    void aRowOnTheLineIsNotOfferedForAPointPastIt() {
        Compilation compiled = compiled("""
                module example.strings

                data No = { why: Int }
                data Yes = { v: Int }
                data Result = No | Yes

                behavior cmp : (a: String, b: String) -> Result
                    constructs Yes, No

                let cmp (a, b) = {
                    guard a > b else No { why = 0 }
                    Yes { v = 1 }
                }

                example cmp
                    | "same" : ("b", "b") -> No { why = 0 }
                """);
        Map<String, List<BorderAssessment>> lines =
                Adequacy.searchedBoundariesOf(compiled.db(), "example.strings");
        assertNotNull(lines, "the model under test compiles");

        List<String> sides = new ArrayList<>();
        lines.values().forEach(each -> each.forEach(line -> {
            for (BorderAssessment.Point point : line.points()) {
                if (point.role().againstTheLine() || point.owed() == null) {
                    continue;   // the line itself, and the points nothing is owed at
                }
                sides.add(point.role() + " " + point.against());
                for (ItemAssessment.Attempt attempt : point.owed().searches().each()) {
                    if (!(attempt instanceof ItemAssessment.Attempt.Built built)) {
                        continue;
                    }
                    List<String> wrote = built.row().inputs().stream()
                            .map(FixtureTemplate::text).toList();
                    assertNotEquals(wrote.get(0), wrote.get(1),
                            () -> "a pair standing equal is the line itself and is at neither side"
                                    + " of it, and this one is offered for " + point.against()
                                    + ": " + wrote);
                }
            }
        }));
        assertFalse(sides.isEmpty(),
                "the sides of the line this reads, which are what the rows above are offered for");
    }

    /**
     * A side the rules leave one value wide has no point away from the border.
     *
     * <p>The same reason as a bound's far side, one arity up: every value an {@code IN} point could
     * be written at is one the rules refuse. Against a guard three values further out, where the
     * side holds values and the point is owed.
     */
    @Test
    void aSideTheRulesLeaveOneValueWideOwesNoPointAwayFromTheBorder() {
        assertEquals(new souther.compiler.query.ItemAssessment.NotOwed(
                        NotOwedReason.NO_VALUE_CAN_STAND_THERE),
                bordersOf(model("Int", ">= 0", "<= 0", "0")).get("h.a = 0").at(PointRole.IN),
                "nothing is inside `0 <= x <= 0` and away from its border");
        assertEquals("in 0 <= h.a < 3",
                inside(bordersOf(model("Int", ">= 0", "<= 3", "1")).get("h.a = 3")),
                "and three values further out the side holds values");
    }

    /**
     * A line between two positions owes all four points, and no two of them hold one pair.
     *
     * <p>Such a line is a border on the difference the two terms fall apart by, so its points are
     * ordinary: under {@code a < b} the pair where {@code a} is {@code b} less one is inside the
     * border and against it, which is its {@code ON} point, and the pairs further under that are its
     * {@code IN} point. Read as {@code a < b} against {@code a = b} with no step, the two came out
     * as one set — a row at the {@code ON} point was counted as the point away from the border, and
     * the point against it was reported as one nothing could name.
     *
     * <p>Both spellings, because the four move together. An expectation on the strict one alone
     * holds against a reading that puts every point one step the wrong way.
     */
    @Test
    void aLineBetweenTwoPositionsOwesFourPointsThatNoOnePairSatisfiesTwice() {
        assertEquals(List.of("ON: = p.b - 1", "OFF: = p.b", "IN: in p.a < p.b - 1",
                        "OUT: in p.b < p.a"),
                pointsOf(comparing("<")),
                "an open border is at its own OFF point, with the ON point one step inside it");
        assertEquals(List.of("ON: = p.b", "OFF: = p.b + 1", "IN: in p.a < p.b",
                        "OUT: in p.b + 1 < p.a"),
                pointsOf(comparing("<=")),
                "a closed border is at its own ON point, with the OFF point one step outside it");
    }

    /**
     * A row offered for a point puts that point's own coverage where it was missing.
     *
     * <p>The invariant the four criteria above do not state. What a point asks of a row and what a
     * search composes to stand for it are two answers, and holding only the first let a side be
     * offered the pair against the line: the row was labelled for the side, carried the values of
     * the point beside it, and an author who pasted it and measured again found the item still
     * uncovered — and was offered the same row next time.
     *
     * <p>Written as pasting the row back, because that is what an author does with it. Read as the
     * values the search settled on, this passes on any arithmetic that agrees with itself.
     *
     * <p>All four spellings, since the four points move together and each spelling puts a different
     * one of them on the line.
     */
    @Test
    void aRowOfferedForAPointCoversThatPointWhenItIsPastedBack() {
        for (String op : List.of("<", "<=", ">", ">=")) {
            String model = comparing(op);
            // Every point that is owed and has no row is one a row is offered for. Held first,
            // because what a wrong candidate becomes once it is checked is no candidate at all: a
            // side offered the pair against the line composes nothing rather than composing that
            // pair, and a check that walked only the rows it was given would see a point go quiet.
            assertEquals(uncovered(model), offeredFor(model).keySet(),
                    () -> "every uncovered point of `guard a " + op + " b` is offered a row");
            for (Map.Entry<String, String> offered : offeredFor(model).entrySet()) {
                String point = offered.getKey();
                Map<String, BorderAssessment> after = bordersOf(withRow(model, offered.getValue()));
                BorderAssessment line = after.get("p.a = p.b");
                assertNotNull(line, after.keySet().toString());
                PointRole role = java.util.stream.Stream.of(PointRole.values())
                        .filter(each -> point.equals(line.label(each)))
                        .findFirst().orElseThrow(() -> new AssertionError(
                                "the row was offered for " + point + ", which this line has no"
                                        + " point of: " + after.keySet()));
                assertTrue(line.owedAt(role).hasRowWitness(),
                        () -> "a row offered for `" + point + "` of `guard a " + op + " b` does not"
                                + " cover it: " + offered.getValue());
            }
        }
    }

    /**
     * A side of such a line is offered a row over a carrier that names no next value.
     *
     * <p>The point against the line is not, and that is the difference. A `Decimal` names no value
     * one step from anything, so the two points against the line are not named at all; the two sides
     * are ordinary — every pair where one is under the other is in one of them — and asking the
     * carrier for the nearest pair is asking it the wrong question. Answered that way, `a < b` over
     * decimals had both of its sides owed and neither of them offered a row, and the block said
     * nothing composes one about a pair anybody could write by hand.
     */
    @Test
    void aSideOfALineOverACarrierWithNoNextValueIsStillOfferedARow() {
        String model = comparing("<").replace("a: Int, b: Int", "a: Decimal, b: Decimal")
                .replace("a = 3, b = 3", "a = 3m, b = 3m");
        BorderAssessment line = bordersOf(model).get("p.a = p.b");
        assertNotNull(line, bordersOf(model).keySet().toString());

        assertEquals(new souther.compiler.query.ItemAssessment.NotOwed(
                        NotOwedReason.THE_CARRIER_NAMES_NO_NEIGHBOUR), line.at(PointRole.ON),
                "a decimal names no pair one step inside the line");
        assertEquals(java.util.Set.of("p.a < p.b", "p.b < p.a"), offeredFor(model).keySet(),
                "and both sides of it are pairs this composes, being sets rather than nearest"
                        + " anything");
    }

    /** Each point of this model's line that is owed a row and has none, as the report labels it. */
    private static java.util.Set<String> uncovered(String model) {
        BorderAssessment line = bordersOf(model).get("p.a = p.b");
        assertNotNull(line, bordersOf(model).keySet().toString());
        return java.util.stream.Stream.of(PointRole.values())
                .filter(role -> line.owedAt(role) != null)
                .filter(role -> !line.owedAt(role).hasRowWitness())
                .map(line::label)
                .collect(java.util.stream.Collectors.toCollection(java.util.LinkedHashSet::new));
    }

    /** Every row this model is offered for its line between two positions, by the point it is
     *  offered for. */
    private static Map<String, String> offeredFor(String model) {
        Adequacy.Filling filling = compiled(model).db()
                .ask(new Adequacy.Generated("example.owed", "cmp")).value();
        assertNotNull(filling, "the model under test compiles");
        Map<String, String> out = new java.util.LinkedHashMap<>();
        filling.boundaries().rows().forEach(row -> out.put(String.join(" x ", row.labels()),
                row.inputs().stream().map(FixtureTemplate::text)
                        .collect(java.util.stream.Collectors.joining(", "))));
        assertFalse(out.isEmpty(), "the model under test is offered rows at its line");
        return out;
    }

    /** The same model with one more row written at {@code inputs}. */
    private static String withRow(String model, String inputs) {
        return model + "    | \"offered\" : (" + inputs + ") -> Ok\n";
    }

    /** Each point of the model's one line, as {@code role: relation against}. */
    private static List<String> pointsOf(String model) {
        BorderAssessment line = bordersOf(model).get("p.a = p.b");
        assertNotNull(line, bordersOf(model).keySet().toString());
        return java.util.stream.Stream.of(PointRole.ON, PointRole.OFF, PointRole.IN, PointRole.OUT)
                .map(role -> role + ": " + line.operator(role) + " " + line.against(role)).toList();
    }

    /** Two whole numbers of one record, compared. */
    private static String comparing(String op) {
        return """
                module example.owed

                data P = { a: Int, b: Int }

                data Ok
                data No
                data Verdict = Ok | No

                behavior cmp : (p: P) -> Verdict
                let cmp (p) = { guard p.a %s p.b else Ok
                    No }

                example cmp
                    | "on the line" : (P { a = 3, b = 3 }) -> Ok
                """.formatted(op);
    }

    /**
     * A point a row already sits at is not a point a search came back empty from.
     *
     * <p>The two answers are about different things and both reach an author: what the rows showed
     * is a verdict, and what was tried is what {@code --generate} prints. A side of a line between
     * two positions is the one point this compiler composes nothing for, and answered as a search
     * that ran and failed it put a reason under every such side on every run — including the sides a
     * row is in and the sides nothing measured, which is the specific work a person is handed that
     * they may already have done.
     */
    @Test
    void aPointARowIsAlreadyAtIsNotOneASearchCameBackEmptyFrom() {
        Map<String, BorderAssessment> borders = bordersOf(BOTH_SIDES);
        BorderAssessment line = borders.get("p.a = p.b");
        assertNotNull(line, borders.keySet().toString());

        // Well under and well over, which is what the two points away from the border ask for. A
        // row one step under the line is the ON point rather than the IN point, and a test written
        // with one would be asserting about the point beside the one it names.
        assertTrue(line.owedAt(PointRole.IN).hasRowWitness(), "a row is well under the line");
        assertTrue(line.owedAt(PointRole.OUT).hasRowWitness(), "and one is well over it");
        for (PointRole role : List.of(PointRole.IN, PointRole.OUT)) {
            assertFalse(line.owedAt(role).worthSearching(), role.toString());
            assertFalse(line.owedAt(role).searches().ran(), role.toString());
        }

        // And the block an author reads says nothing about them, because nothing is owed there.
        String block = souther.compiler.report.GeneratedRows.of(
                compiled(BOTH_SIDES), "example.owed", "cmp", SourceRendering.namedByIdentity(SourceLayouts.NONE)).text();
        assertFalse(block.contains("p.a < p.b"), block);
        assertFalse(block.contains("p.a > p.b"), block);
    }

    /** A line between two positions with a row either side of it and none on it. */
    private static final String BOTH_SIDES = """
            module example.owed

            data P = { a: Int, b: Int }

            data Ok
            data No
            data Verdict = Ok | No

            behavior cmp : (p: P) -> Verdict
            let cmp (p) = { guard p.a < p.b else Ok
                No }

            example cmp
                | "well under" : (P { a = 1, b = 5 }) -> No
                | "well over" : (P { a = 5, b = 1 }) -> Ok
            """;

    /** What a row inside this border has to do, as the report writes it. */
    private static String inside(BorderAssessment border) {
        return border.operator(PointRole.IN) + " " + border.against(PointRole.IN);
    }

    /** Every border of the one behavior {@code model} declares, by the line it is at. */
    private static Map<String, BorderAssessment> bordersOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> boundaries =
                Adequacy.boundariesOf(compilation.db(), "example.owed");
        assertNotNull(boundaries, "the model under test compiles");
        Map<String, BorderAssessment> out = new java.util.LinkedHashMap<>();
        boundaries.values().forEach(each -> each.forEach(b -> out.put(b.label(), b)));
        return out;
    }

    private static Compilation compiled(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }
}
