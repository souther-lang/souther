package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.Generator;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A total of what each element comes to as fields added or taken away is written wherever the
 * fields' runs reach it: a row of one element whose fields are each somewhere in their runs comes
 * to every number from the least the form takes to the greatest. The reading of the comparison
 * says the total takes those values, and each is a row the builder writes, at the line, at both
 * ends of what one element reaches.
 *
 * <p>Fields at nought to five: {@code p - q} comes to every whole number from minus five to five,
 * and {@code p + q - r} to every one from minus five to ten. Five is written with {@code q} at
 * nought, which a field held at one does not reach.
 */
class ATotalOfFieldsTakenOneFromAnotherIsWrittenWhereverTheFieldsReachItTest {

    private static final String MODEL = """
            module w1
            data F = Int
                invariant value >= 0 && value <= 5
            data L = { p: F, q: F, r: F }
            data One = { ls: List<L> }
                invariant List.length(ls) <= 1
            behavior m : (b: One) -> Bool
            let m (b) = List.sum(List.map(l -> %s, b.ls)) %s
            """;

    private static final Pattern ELEMENT = Pattern.compile(
            "L \\{ p = F\\((-?\\d+)\\), q = F\\((-?\\d+)\\), r = F\\((-?\\d+)\\) }");

    private static final String DIFFERENCE = "l.p.value - l.q.value";

    private static final String THREE = "l.p.value + l.q.value - l.r.value";

    @Test
    void theEndsOfADifferenceOfTwoFieldsAreWritten() {
        assertWrittenAt(DIFFERENCE, "List.sum({1·p + -1·q + 0 | b.ls[*]})", ">= 5", 5);
        assertWrittenAt(DIFFERENCE, "List.sum({1·p + -1·q + 0 | b.ls[*]})", "<= -5", -5);
    }

    @Test
    void theEndsOfASumOfThreeFieldsOneTakenAwayAreWritten() {
        assertWrittenAt(THREE, "List.sum({1·p + 1·q + -1·r + 0 | b.ls[*]})", ">= 10", 10);
        assertWrittenAt(THREE, "List.sum({1·p + 1·q + -1·r + 0 | b.ls[*]})", "<= -5", -5);
    }

    private static final String DECIMALS = """
            module w1
            data Fraction = Decimal
                invariant value >= 0.2m && value <= 0.8m
            data L = { p: Fraction, q: Fraction }
            data One = { ls: List<L> }
                invariant List.length(ls) <= 1
            behavior m : (b: One) -> Bool
            let m (b) = Decimal.compare(List.sum(List.map(l -> Decimal.add(l.p.value, l.q.value),
                                                          b.ls)), %s) %s
            """;

    private static final Pattern FRACTIONS = Pattern.compile(
            "L \\{ p = Fraction\\(([0-9.]+)m\\), q = Fraction\\(([0-9.]+)m\\) }");

    /**
     * Two fields of two to eight tenths come to every number from four tenths to one and six
     * tenths, and a row is written at both ends: the field held still is held at a decimal of
     * its run, which holds no whole number.
     */
    @Test
    void theEndsOfASumOfTwoFieldsOfDecimalsAreWritten() {
        assertDecimalsWrittenAt(DECIMALS.formatted("1.6m", ">= 0"), "1.6", "0.2");
        assertDecimalsWrittenAt(DECIMALS.formatted("0.4m", "<= 0"), "0.4", "0.2");
    }

    /**
     * Fields between two and eight tenths, both ends left out, come to one: the field held still
     * is held at the decimal a row is built at inside its run nearest the end, and not at an end
     * no value of the run stands at.
     */
    @Test
    void aSumOfTwoFieldsOfDecimalsWithTheirEndsLeftOutIsWritten() {
        assertDecimalsWrittenAt(DECIMALS
                .replace("value >= 0.2m && value <= 0.8m", "value > 0.2m && value < 0.8m")
                .formatted("1.0m", ">= 0"), "1", "0.2");
    }

    private static final String DECIMAL_TOTAL = "List.sum({1·p + 1·q + 0 | b.ls[*]})";

    /**
     * That a row is offered for the point of the total at {@code at} in {@code model}, and that
     * every row offered for it comes to {@code at} with each field past {@code above}, unless it
     * is written there.
     */
    private static void assertDecimalsWrittenAt(String model, String at, String above) {
        Generator.GenerationResult offered = offeredFor(model);
        BigDecimal point = new BigDecimal(at);
        boolean written = false;
        for (Generator.GeneratedRow row : offered.rows()) {
            boolean forThePoint = row.purposes().stream().anyMatch(purpose ->
                    purpose instanceof Generator.Purpose.ForAPoint each
                            && each.label().equals(DECIMAL_TOTAL + " = " + at));
            if (!forThePoint) {
                continue;
            }
            Matcher element = FRACTIONS.matcher(row.inputs().getFirst().text());
            BigDecimal sum = BigDecimal.ZERO;
            while (element.find()) {
                BigDecimal p = new BigDecimal(element.group(1));
                BigDecimal q = new BigDecimal(element.group(2));
                assertTrue(p.compareTo(new BigDecimal(above)) >= 0
                        && q.compareTo(new BigDecimal(above)) >= 0, row.inputs().getFirst()::text);
                sum = sum.add(p).add(q);
            }
            assertEquals(0, sum.compareTo(point), row.inputs().getFirst()::text);
            written = true;
        }
        assertTrue(written, () -> at + " is written by no row: " + offered.unresolved());
    }

    private static final String COUNTED = """
            module w1
            data F = Int
                invariant value >= 1 && value <= 3
            data L = { p: F, q: F }
            data One = { ls: List<L> }
                invariant %s
            behavior m : (b: One) -> Bool
            let m (b) = List.sum(List.map(l -> l.p.value + l.q.value, b.ls)) %s
            """;

    private static final Pattern TWO_FIELDS =
            Pattern.compile("L \\{ p = F\\((\\d+)\\), q = F\\((\\d+)\\) }");

    /**
     * Fields of one to three, in a container of two or of two or more, come to five, which one
     * element also comes to: the field held still is held for the count the container holds, so
     * two elements are written coming to five, and no element of one.
     */
    @Test
    void theFieldsHeldStillAreHeldForTheCountTheContainerHolds() {
        for (String count : List.of("List.length(ls) == 2", "List.length(ls) >= 2")) {
            List<String> rows = rowsAt(COUNTED.formatted(count, ">= 5"), DECIMAL_TOTAL + " = 5");
            assertFalse(rows.isEmpty(), count);
            for (String row : rows) {
                Matcher element = TWO_FIELDS.matcher(row);
                int elements = 0;
                int sum = 0;
                while (element.find()) {
                    elements++;
                    sum += Integer.parseInt(element.group(1)) + Integer.parseInt(element.group(2));
                }
                assertTrue(elements >= 2, row);
                assertEquals(5, sum, row);
            }
        }
    }

    /**
     * Fields of one to three come to nought only in a container of none, which holds no field
     * to hold still: written where the container may hold none, and where it holds none at all.
     */
    @Test
    void aContainerOfNoneIsWrittenForATotalOfNought() {
        for (String count : List.of("List.length(ls) <= 2", "List.length(ls) == 0")) {
            List<String> rows = rowsAt(COUNTED.formatted(count, "<= 0"), DECIMAL_TOTAL + " = 0");
            assertEquals(List.of("One { ls = [] }"), rows.stream().distinct().toList(), count);
        }
    }

    /**
     * What each element comes to chosen on a flag of it, which no field is solved for: the list of
     * none still comes to nought, and is written there, with no element to work it out of.
     */
    @Test
    void aListOfNoneIsWrittenForATotalNoFieldOfWhichIsSolvedFor() {
        String model = """
                module w1
                data F = Int
                    invariant value >= 1 && value <= 3
                data L = { flag: Bool, p: F, q: F }
                data One = { ls: List<L> }
                    invariant List.length(ls) <= 2
                behavior m : (b: One) -> Bool
                let m (b) = List.sum(List.map(l -> if l.flag then l.p.value else l.q.value,
                                              b.ls)) <= 0
                """;
        Generator.GenerationResult offered = offeredFor(model);
        List<String> rows = offered.rows().stream()
                .filter(row -> row.purposes().stream().anyMatch(purpose ->
                        purpose instanceof Generator.Purpose.ForAPoint point
                                && point.label().startsWith("List.sum(")
                                && point.label().endsWith(" = 0")))
                .map(row -> row.inputs().getFirst().text()).distinct().toList();
        assertEquals(List.of("One { ls = [] }"), rows, () -> offered.rows().stream()
                .map(row -> row.purposes() + " " + row.inputs().getFirst().text()).toList()
                + " " + offered.unresolved());
    }

    /** The first input of each row offered for the point {@code label} in {@code model}. */
    private static List<String> rowsAt(String model, String label) {
        Generator.GenerationResult offered = offeredFor(model);
        List<String> rows = offered.rows().stream()
                .filter(row -> row.purposes().stream().anyMatch(purpose ->
                        purpose instanceof Generator.Purpose.ForAPoint point
                                && point.label().equals(label)))
                .map(row -> row.inputs().getFirst().text()).toList();
        assertFalse(rows.isEmpty(), () -> label + " is written by no row: " + offered.unresolved());
        return rows;
    }

    /**
     * Twelve fields of nought to one come to twelve only with every one at one: eleven held and
     * one solved for, each held at the value the total leaves it, and no way of holding them is
     * searched for.
     */
    @Test
    void manyFieldsHeldStillAreWorkedOutOfTheTotal() {
        StringBuilder fields = new StringBuilder();
        StringBuilder sum = new StringBuilder();
        for (int i = 0; i < 12; i++) {
            fields.append(i == 0 ? "" : ", ").append("f").append(i).append(": Bit");
            sum.append(i == 0 ? "" : " + ").append("l.f").append(i).append(".value");
        }
        String model = """
                module w1
                data Bit = Int
                    invariant value >= 0 && value <= 1
                data L = { %s }
                data One = { ls: List<L> }
                    invariant List.length(ls) <= 1
                behavior m : (b: One) -> Bool
                let m (b) = List.sum(List.map(l -> %s, b.ls)) >= 12
                """.formatted(fields, sum);
        Generator.GenerationResult offered = offeredFor(model);
        assertTrue(offered.rows().stream().anyMatch(row -> row.purposes().stream().anyMatch(
                purpose -> purpose instanceof Generator.Purpose.ForAPoint point
                        && point.label().endsWith(" = 12"))), () -> offered.unresolved().toString());
    }

    /** The total of {@code part} compared as {@code compared}, whose line is at {@code line}: a
     *  row is offered there, and it comes to what the point names. */
    private static void assertWrittenAt(String part, String total, String compared, long line) {
        Generator.GenerationResult offered = offeredFor(MODEL.formatted(part, compared));
        List<String> atTheLine = new ArrayList<>();
        for (Generator.GeneratedRow row : offered.rows()) {
            for (Generator.Purpose purpose : row.purposes()) {
                if (purpose instanceof Generator.Purpose.ForAPoint point
                        && point.label().equals(total + " = " + line)) {
                    atTheLine.add(row.inputs().toString());
                    assertEquals(line, totalOf(part, row), row.inputs()::toString);
                }
            }
        }
        assertFalse(atTheLine.isEmpty(), () -> "no row is written at " + line + " for " + part
                + ": " + offered.unresolved());
    }

    /** What the elements of {@code row} come to under {@code part}; nought where it holds none. */
    private static long totalOf(String part, Generator.GeneratedRow row) {
        Matcher element = ELEMENT.matcher(row.inputs().getFirst().text());
        long total = 0;
        while (element.find()) {
            long p = Long.parseLong(element.group(1));
            long q = Long.parseLong(element.group(2));
            long r = Long.parseLong(element.group(3));
            total += part.equals(DIFFERENCE) ? p - q : p + q - r;
        }
        return total;
    }

    private static Generator.GenerationResult offeredFor(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        return OfferedAtTheLines.of(compilation, compilation.modules().get(0), "m");
    }
}
