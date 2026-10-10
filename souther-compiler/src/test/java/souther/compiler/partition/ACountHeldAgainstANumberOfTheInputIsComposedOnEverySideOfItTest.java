package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many elements of a list meet a statement, held against a number the input holds, is one
 * quantity: the count plus the number's form. A row is composed on each side of where it comes out
 * at the level the rule cuts it at, and the count a condition on the way asks of a row is the one
 * that goes with the numbers the row places beside it.
 */
class ACountHeldAgainstANumberOfTheInputIsComposedOnEverySideOfItTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** One row as a list of strings and the whole numbers beside it. */
    private record Row(List<String> elements, List<Integer> numbers) {

        long meeting(Predicate<String> statement) {
            return elements.stream().filter(statement).count();
        }
    }

    private static final Predicate<String> IS_A = "a"::equals;

    private static final Predicate<String> IS_B = "b"::equals;

    /** Every point of the line is a row, over strings and over numbers alike. */
    @Test
    void aCountAgainstANumberHasARowAtTheLineAndOnEachSideOfIt() {
        for (String statement : List.of("y == \"a\"", "y == \"b\"")) {
            List<Row> rows = rowsOf("""
                    module probe
                    data Low
                    data High
                    behavior pick : (xs: List<String>, n: Int) -> Low | High
                    let pick (xs, n) =
                        if List.length(List.filter(y -> %s, xs)) >= n then High else Low
                    """.formatted(statement));
            Predicate<String> counted = statement.contains("\"a\"") ? IS_A : IS_B;
            Set<Long> apart = differences(rows, counted, 0);
            assertTrue(apart.contains(0L), () -> "a row at the line: " + rows);
            assertTrue(apart.contains(-1L), () -> "a row just short of it: " + rows);
            assertTrue(apart.stream().anyMatch(each -> each > 0), () -> "a row past it: " + rows);
            assertTrue(apart.stream().anyMatch(each -> each < -1),
                    () -> "a row well short of it: " + rows);
        }
    }

    @Test
    void aCountOfNumbersAgainstANumberIsComposedToo() {
        List<Row> rows = rowsOf("""
                module probe
                data Low
                data High
                behavior pick : (xs: List<Int>, n: Int) -> Low | High
                let pick (xs, n) =
                    if List.length(List.filter(y -> y > 0, xs)) >= n then High else Low
                """);
        Set<Long> apart = new LinkedHashSet<>();
        for (Row row : rows) {
            apart.add(row.elements().stream().filter(each -> Integer.parseInt(each) > 0).count()
                    - row.numbers().getFirst());
        }
        assertTrue(apart.contains(0L) && apart.contains(-1L), () -> "both sides: " + rows);
    }

    /** What the rule holds the count against beside the number moves the line and nothing else. */
    @Test
    void aNumberAddedToTheOtherSideMovesTheLine() {
        List<Row> rows = rowsOf("""
                module probe
                data Low
                data High
                behavior pick : (xs: List<String>, n: Int) -> Low | High
                let pick (xs, n) =
                    if List.length(List.filter(y -> y == "a", xs)) >= n + 1 then High else Low
                """);
        Set<Long> apart = differences(rows, IS_A, 0);
        assertTrue(apart.contains(1L), () -> "a row at the line, a count one past n: " + rows);
        assertTrue(apart.contains(0L), () -> "a row just short of it: " + rows);
    }

    /** {@code count >= n} and {@code 2 * count >= 2 * n} are one quantity, and one line on it. */
    @Test
    void aMultipleOfTheRuleCutsTheSameQuantity() {
        String once = quantityOf("List.length(List.filter(y -> y == \"a\", xs)) >= n");
        String twice = quantityOf("2 * List.length(List.filter(y -> y == \"a\", xs)) >= 2 * n");
        String turned = quantityOf("n <= List.length(List.filter(y -> y == \"a\", xs))");
        assertEquals(once, twice);
        assertEquals(once, turned);
    }

    /** The count a condition on the way asks for goes with the number the row places. */
    @Test
    void aCountOnTheWayToAnotherBorderIsMetByTheRowsThatReachIt() {
        List<Row> rows = rowsOf("""
                module probe
                data Low
                data High
                behavior pick : (xs: List<String>, n: Int, k: Int) -> Low | High
                let pick (xs, n, k) =
                    if List.length(List.filter(y -> y == "a", xs)) >= n + 3
                        then (if k > 0 then High else Low) else Low
                """);
        List<Row> past = rows.stream().filter(row -> row.numbers().get(1) > 0).toList();
        assertFalse(past.isEmpty(), () -> "a row on each side of k: " + rows);
        past.forEach(row -> assertTrue(row.meeting(IS_A) >= row.numbers().getFirst() + 3,
                () -> "a row past k stands where the count holds: " + row));
        assertTrue(rows.stream().anyMatch(row -> row.numbers().get(1) <= 0
                        && row.meeting(IS_A) >= row.numbers().getFirst() + 3),
                () -> "and k at its other side with the count held: " + rows);
    }

    /** The one number is shared by two counts of one list, which is one list. */
    @Test
    void twoCountsOfOneListAgainstOneNumberAreComposedInOneList() {
        List<Row> rows = rowsOf("""
                module probe
                data Low
                data High
                behavior pick : (xs: List<String>, n: Int, k: Int) -> Low | High
                let pick (xs, n, k) =
                    if n > 0 then
                        (if List.length(List.filter(y -> y == "a", xs)) >= n then
                            (if List.length(List.filter(y -> y == "b", xs)) >= n then
                                (if k > 0 then High else Low)
                            else Low)
                        else Low)
                    else Low
                """);
        assertTrue(rows.stream().anyMatch(row -> row.numbers().get(1) > 0
                        && row.numbers().getFirst() > 0
                        && row.meeting(IS_A) >= row.numbers().getFirst()
                        && row.meeting(IS_B) >= row.numbers().getFirst()),
                () -> "a row past both counts: " + rows);
    }

    private static Set<Long> differences(List<Row> rows, Predicate<String> counted, int number) {
        Set<Long> out = new LinkedHashSet<>();
        for (Row row : rows) {
            out.add(row.meeting(counted) - row.numbers().get(number));
        }
        return out;
    }

    /** The quantity the one border of a rule is on, as the report names it. */
    private static String quantityOf(String condition) {
        JsonNode report = reportOf("""
                module probe
                data Low
                data High
                behavior pick : (xs: List<String>, n: Int) -> Low | High
                let pick (xs, n) = if %s then High else Low
                """.formatted(condition));
        List<String> axes = new ArrayList<>();
        collect(report, axes);
        assertEquals(1, axes.size(), () -> "one line on the count: " + axes);
        return axes.getFirst();
    }

    private static void collect(JsonNode node, List<String> axes) {
        if (node.isObject() && node.has("items")
                && "count_of_elements".equals(node.path("kind").asString())) {
            axes.add(node.path("axis").asString());
        }
        node.forEach(child -> collect(child, axes));
    }

    private static JsonNode reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
    }

    /** Every row the examples generated for {@code source} write. */
    private static List<Row> rowsOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String text = GeneratedRows.of(compilation, "probe", null,
                SourceRendering.namedByIdentity(SourceLayouts.NONE)).text();
        List<Row> out = new ArrayList<>();
        Matcher row = Pattern.compile("\\(\\[([^\\]]*)\\]((?:,\\s*-?\\d+)+)\\)\\s*->").matcher(text);
        while (row.find()) {
            List<String> elements = new ArrayList<>();
            Matcher each = Pattern.compile("\"((?:[^\"\\\\]|\\\\.)*)\"|(-?\\d+)")
                    .matcher(row.group(1));
            while (each.find()) {
                elements.add(each.group(1) != null ? each.group(1) : each.group(2));
            }
            List<Integer> numbers = new ArrayList<>();
            Matcher number = Pattern.compile("-?\\d+").matcher(row.group(2));
            while (number.find()) {
                numbers.add(Integer.parseInt(number.group()));
            }
            out.add(new Row(elements, numbers));
        }
        assertFalse(out.isEmpty(), () -> "rows were generated: " + text);
        return out;
    }
}
