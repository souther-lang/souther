package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Offering;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An equality between a number and a weighed one is true at the values the weighing reaches and
 * false at every other, and the number's values are told by that: {@code x * 2 == cap} is true at
 * the even {@code cap} and false at the odd.
 *
 * <p>Asked of the rows the classes are offered, which is where a class is a claim about numbers: a
 * row written for the class where the equality can hold has a value of the class, and one written
 * for the class where it never holds has none that the weighing reaches. A bound a type has is a
 * value the rows are asked at, as is the one beside it.
 */
class AnEquationBesideAWeighedNumberIsToldByWhatTheWeighingReachesTest {

    private static final String LINE = "data Line = { qty: Int, code: String }\n";

    private static final String ITEM = """
            data Item = { v: Int }
                invariant low = v >= 0
                invariant high = v <= 10
            """;

    private static final String DOUBLED = "List.sum(List.map(x -> x * 2, xs))";
    private static final String FILTERED = "List.sum(List.map(l -> l.qty,"
            + " List.filter(l -> l.qty > 5, lines)))";
    private static final String BOUNDED = "List.sum(List.map(i -> i.v * 2, items))";

    private static final Pattern CAP = Pattern.compile("\\(.*?(-?\\d+)\\)\\s*->");

    private static String model(String declarations, String parameters, String body) {
        return """
                module probe
                %s
                behavior check : (%s, cap: Int) -> Bool
                let check (%s, cap) = %s
                """.formatted(declarations, parameters,
                parameters.substring(0, parameters.indexOf(':')), body);
    }

    /** A model is compiled and measured once, whichever of its report and rows a test asks. */
    private static final Map<String, Compilation> COMPILED = new ConcurrentHashMap<>();

    private static Compilation compile(String model) {
        return COMPILED.computeIfAbsent(model, source -> {
            Compilation compilation = Compilation.ofSource(source, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            return compilation;
        });
    }

    private static String report(String model) {
        Compilation compilation = compile(model);
        return AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static List<RowsOfABlock.Row> rows(String model) {
        Compilation compilation = compile(model);
        Offering offering = Adequacy.offeredFor(compilation.db(),
                OfferingRequest.overTheModule("probe"));
        return RowsOfABlock.of(GeneratedRows.of(offering, Map.of(),
                SourceRendering.namedByIdentity(compilation.texts()), compilation.db())
                .textInEnglish());
    }

    /** The {@code cap} a row writes, which is the last number of its values. */
    private static BigInteger capOf(RowsOfABlock.Row row) {
        Matcher found = CAP.matcher(row.values());
        assertTrue(found.find(), row.values());
        return new BigInteger(found.group(1));
    }

    /** The values {@code cap} is written at in the rows said to be for {@code thing}. */
    private static List<BigInteger> capsFor(List<RowsOfABlock.Row> rows, String thing) {
        return rows.stream().filter(row -> row.isFor(thing)).map(
                AnEquationBesideAWeighedNumberIsToldByWhatTheWeighingReachesTest::capOf).toList();
    }

    private static boolean even(BigInteger value) {
        return !value.testBit(0);
    }

    @Test
    void twiceANumberIsTrueAtTheEvenValuesAndNeverAtTheOdd() {
        String source = model("", "x: Int", "x * 2 == cap").replace("(x, cap) = x", "(x, cap) = x");
        String said = report(source);
        assertFalse(said.contains("not read"), said);
        assertTrue(said.contains("cap is divided by"), said);
        List<RowsOfABlock.Row> rows = rows(source);
        List<BigInteger> canBe = capsFor(rows, "cap: cap can be 2 * x at cap");
        assertFalse(canBe.isEmpty(), rows.toString());
        canBe.forEach(cap -> assertTrue(even(cap), "can be " + cap));
        capsFor(rows, "cap: cap is never 2 * x at cap")
                .forEach(cap -> assertFalse(even(cap), "never " + cap));
    }

    /** The least of the type is an even number and twice a number of it, so it is a value the
     *  class is offered; the greatest is odd and no value of the other class is past it. */
    @Test
    void theEndsOfIntAreToldByTheirRemainder() {
        List<RowsOfABlock.Row> rows = rows(model("", "x: Int", "x * 2 == cap"));
        List<BigInteger> canBe = capsFor(rows, "cap: cap can be 2 * x at cap");
        BigInteger least = BigInteger.valueOf(Long.MIN_VALUE);
        assertTrue(canBe.stream().allMatch(cap -> cap.compareTo(least) >= 0), canBe.toString());
        assertEquals(List.of(least), canBe, "the nearest even value to the ends");
    }

    @Test
    void aTotalOfDoubledElementsIsTrueAtTheEvenValuesAndNeverAtTheOdd() {
        String source = model("", "xs: List<Int>", DOUBLED + " == cap");
        String said = report(source);
        assertFalse(said.contains("not read"), said);
        List<RowsOfABlock.Row> rows = rows(source);
        List<BigInteger> canBe = capsFor(rows,
                "cap: cap can be List.sum({2·the element itself + 0 | xs[*]}) at cap");
        assertFalse(canBe.isEmpty(), rows.toString());
        canBe.forEach(cap -> assertTrue(even(cap), "can be " + cap));
    }

    /** A total over what a filter keeps is nought or from the least it keeps, and no value
     *  between, and none below nought. */
    @Test
    void aTotalOverWhatAFilterKeepsIsTrueAtNoughtAndFromSixAndNeverBetween() {
        String source = model(LINE, "lines: List<Line>", FILTERED + " == cap");
        String said = report(source);
        assertFalse(said.contains("not read"), said);
        List<RowsOfABlock.Row> rows = rows(source);
        String sum = "List.sum({if 1·qty + -5 > 0 then 1·qty + 0 else 0 | lines[*]})";
        rows.stream().filter(row -> row.fills().stream()
                .anyMatch(line -> line.startsWith("cap: cap can be " + sum))).forEach(row -> {
                    BigInteger cap = capOf(row);
                    assertTrue(cap.signum() == 0 || cap.compareTo(BigInteger.valueOf(6)) >= 0,
                            "can be " + cap);
                });
        rows.stream().filter(row -> row.fills().stream()
                .anyMatch(line -> line.startsWith("cap: cap is never " + sum))).forEach(row -> {
                    BigInteger cap = capOf(row);
                    assertTrue(cap.signum() < 0
                            || (cap.signum() > 0 && cap.compareTo(BigInteger.valueOf(6)) < 0),
                            "never " + cap);
                });
    }

    /** What several elements add up to is the evens from nought, so an even value past what one
     *  element reaches is not said to be none of the totals. */
    @Test
    void aValueOnlySeveralBoundedElementsReachIsNotSaidToBeUnreachable() {
        String source = model(ITEM, "items: List<Item>", BOUNDED + " == cap");
        List<RowsOfABlock.Row> rows = rows(source);
        String sum = "List.sum({2·v + 0 | items[*]})";
        rows.stream().filter(row -> row.isFor("cap: cap is never " + sum + " at cap")
                || row.fills().stream().anyMatch(line -> line.startsWith("cap: cap is never")))
                .forEach(row -> assertFalse(even(capOf(row)),
                        "even " + capOf(row) + " is a total of some elements: " + row.values()));
    }

    /** The two comparisons of one position part it together: by the weighing and by the line. */
    @Test
    void aLineAndAWeighedEqualityPartOnePositionTogether() {
        String source = model("", "x: Int", "x * 2 == cap && cap > 10");
        List<RowsOfABlock.Row> rows = rows(source);
        capsFor(rows, "cap: cap <= 10 and cap can be 2 * x at cap").forEach(cap -> {
            assertTrue(even(cap), "can be " + cap);
            assertTrue(cap.compareTo(BigInteger.TEN) <= 0, "at most ten " + cap);
        });
        capsFor(rows, "cap: cap > 10 and cap is never 2 * x at cap").forEach(cap -> {
            assertFalse(even(cap), "never " + cap);
            assertTrue(cap.compareTo(BigInteger.TEN) > 0, "past ten " + cap);
        });
        assertFalse(capsFor(rows, "cap: cap > 10 and cap is never 2 * x at cap").isEmpty(),
                rows.toString());
    }

    /** The rows said to be for a class whose name starts {@code prefix}, by name or by what is
     *  said over them. */
    private static List<RowsOfABlock.Row> rowsOfTheClass(List<RowsOfABlock.Row> rows,
                                                        String prefix) {
        return rows.stream().filter(row -> row.name().orElse("").startsWith(prefix)
                || row.fills().stream().anyMatch(line -> line.startsWith(prefix))).toList();
    }

    /** What {@code x * 2 /= cap} leaves of {@code cap} is what {@code ==} leaves: the equality is
     *  what is told apart, and which way a row comes out is the borders'. */
    @Test
    void anInequalityPartsTheNumberByTheSameValues() {
        List<RowsOfABlock.Row> rows = rows(model("", "x: Int", "x * 2 /= cap"));
        String said = report(model("", "x: Int", "x * 2 /= cap"));
        assertFalse(said.contains("not read"), said);
        capsFor(rows, "cap: cap can be 2 * x at cap")
                .forEach(cap -> assertTrue(even(cap), "can be " + cap));
        rowsOfTheClass(rows, "cap: cap is never 2 * x")
                .forEach(row -> assertFalse(even(capOf(row)), "never " + row.values()));
    }

    /** A negative weight and a constant: {@code 1 - 3x} is one more than a multiple of three. */
    @Test
    void aNegativeWeightAndAConstantLeaveTheNumbersTheyReach() {
        List<RowsOfABlock.Row> rows = rows(model("", "x: Int", "1 - x * 3 == cap"));
        List<RowsOfABlock.Row> canBe = rowsOfTheClass(rows, "cap: cap can be");
        assertFalse(canBe.isEmpty(), rows.toString());
        canBe.forEach(row -> assertEquals(1, capOf(row).mod(BigInteger.valueOf(3)).intValue(),
                "can be " + row.values()));
        rowsOfTheClass(rows, "cap: cap is never").forEach(row -> assertTrue(
                capOf(row).mod(BigInteger.valueOf(3)).intValue() != 1, "never " + row.values()));
    }

    /** What a way to the comparison holds {@code x} to is what the equation reaches: past
     *  {@code x >= 0} no negative number is twice {@code x}. */
    @Test
    void aWayThatHoldsTheOtherSideBoundsWhatTheEquationReaches() {
        List<RowsOfABlock.Row> rows = rows(model("", "x: Int",
                "if x >= 0 then x * 2 == cap else false"));
        List<RowsOfABlock.Row> canBe = rowsOfTheClass(rows, "cap: cap can be");
        canBe.forEach(row -> {
            assertTrue(even(capOf(row)), "can be " + row.values());
            assertTrue(capOf(row).signum() >= 0, "no row reaches the equality at " + row.values());
        });
    }

    /** The rows written for the borders are read by running the relation: those at the line are
     *  rows where the two sides are equal, and those off it are rows where they are not. */
    @Test
    void theRowsAtTheLineAreRowsWhereTheSidesAreEqual() {
        List<RowsOfABlock.Row> rows = rows(model("", "x: Int", "x * 2 == cap"));
        Pattern both = Pattern.compile("\\((-?\\d+), (-?\\d+)\\)\\s*->");
        int checked = 0;
        for (RowsOfABlock.Row row : rows) {
            Matcher found = both.matcher(row.values());
            if (!found.find()) {
                continue;
            }
            BigInteger twice = new BigInteger(found.group(1)).shiftLeft(1);
            boolean equal = twice.equals(new BigInteger(found.group(2)));
            if (row.fills().stream().anyMatch(line -> line.startsWith("ON point"))) {
                assertTrue(equal, row.values());
                checked++;
            } else if (row.fills().stream().anyMatch(line -> line.startsWith("OFF point"))) {
                assertFalse(equal, row.values());
                checked++;
            }
        }
        assertTrue(checked >= 2, "the borders were checked: " + rows);
    }

    /**
     * A number whose declarations already enumerate its values keeps those classes, and the
     * equality is decided at each of them: it is not offered as a second list beside them.
     */
    @Test
    void aNumberTheDeclarationsEnumerateKeepsItsClasses() {
        String source = model("""
                data Small = Int
                    invariant small = value == 1 || value == 2 || value == 3
                """, "x: Int", "x * 2 == cap.value").replace("cap: Int", "cap: Small");
        Compilation compilation = compile(source);
        String json = AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts()));
        JsonNode axes = JsonMapper.builder().build().readTree(json).get("modules").get(0)
                .get("behaviors").get(0).get("partition").get("axes");
        List<String> classes = new ArrayList<>();
        for (JsonNode axis : axes) {
            if (axis.get("axis").asString().equals("check/cap")) {
                axis.get("classes").forEach(each -> classes.add(each.asString()));
            }
        }
        assertEquals(List.of("1", "2", "3"), classes, json);
    }

    /** The borders of the equality are what they were. */
    @Test
    void theBordersOfTheEqualityAreAsTheyWere() {
        String said = report(model("", "x: Int", "x * 2 == cap"));
        assertTrue(said.contains("-cap + 2 * x: = 0"), said);
        assertTrue(said.contains("-cap + 2 * x: = -1"), said);
        assertTrue(said.contains("-cap + 2 * x: = 1"), said);
    }
}
