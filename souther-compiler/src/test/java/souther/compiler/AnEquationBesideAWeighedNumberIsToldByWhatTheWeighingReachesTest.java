package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Offering;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import java.math.BigInteger;
import java.util.List;
import java.util.Map;
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

    private static Compilation compile(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
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

    /** The borders of the equality are what they were. */
    @Test
    void theBordersOfTheEqualityAreAsTheyWere() {
        String said = report(model("", "x: Int", "x * 2 == cap"));
        assertTrue(said.contains("-cap + 2 * x: = 0"), said);
        assertTrue(said.contains("-cap + 2 * x: = -1"), said);
        assertTrue(said.contains("-cap + 2 * x: = 1"), said);
    }
}
