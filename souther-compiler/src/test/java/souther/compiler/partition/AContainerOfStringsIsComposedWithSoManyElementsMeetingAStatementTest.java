package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.GeneratedRows;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An element no number stands for — a string — is chosen for a count the way a number is: out of
 * the values the statement asked of it tells apart, so that a container holds as many elements
 * meeting a statement as the count asks.
 */
class AContainerOfStringsIsComposedWithSoManyElementsMeetingAStatementTest {

    /** An equality on a string draws a line at the count, and a row is composed on each side. */
    @Test
    void aCountOfWhatEqualsAStringHasAContainerOnEachSideOfItsLine() {
        List<List<String>> offered = containersOffered("""
                module probe
                data Low
                data High
                behavior pick : (xs: List<String>) -> Low | High
                let pick (xs) = if List.length(List.filter(y -> y == "a", xs)) >= 2 then High else Low
                """);
        assertTrue(offered.stream().anyMatch(holding("a", 1)),
                () -> "one below the line: " + offered);
        assertTrue(offered.stream().anyMatch(holding("a", 2)),
                () -> "one on the line: " + offered);
        assertTrue(offered.stream().anyMatch(holding("a", 3)),
                () -> "one above the line: " + offered);
    }

    /** Where the statement holds a string against an order, the ones either side of it are told
     *  apart. */
    @Test
    void aCountOfWhatIsBelowAStringIsComposedOfStringsOnBothSidesOfIt() {
        List<List<String>> offered = containersOffered("""
                module probe
                data Low
                data High
                behavior pick : (xs: List<String>) -> Low | High
                let pick (xs) = if List.length(List.filter(y -> y < "m", xs)) >= 2 then High else Low
                """);
        assertTrue(offered.stream().anyMatch(below("m", 1)), () -> "one below: " + offered);
        assertTrue(offered.stream().anyMatch(below("m", 2)), () -> "two below: " + offered);
        assertTrue(offered.stream().anyMatch(below("m", 0)
                .and(values -> !values.isEmpty())), () -> "one with none below: " + offered);
    }

    /**
     * Strings of a type kept to one letter at least are chosen out of what the type admits: the
     * least string along the order is the empty one, which every row holding it is refused for,
     * so the ones chosen below the string the statement holds them against are strings of the
     * type there. Alike where the string is a field of the element.
     */
    @Test
    void aCountOfWhatIsBelowAStringIsComposedOfStringsTheirTypeAdmits() {
        String labels = """
                module probe
                data Low
                data High
                data Label = String
                    invariant String.length(value) >= 1
                """;
        String alone = labels + """
                behavior pick : (xs: List<Label>) -> Low | High
                let pick (xs) =
                    if List.length(List.filter(y -> y.value < "m", xs)) >= 2 then High else Low
                """;
        String inARecord = labels + """
                data Item = { label: Label, size: Int }
                behavior pick : (xs: List<Item>) -> Low | High
                let pick (xs) =
                    if List.length(List.filter(y -> y.label.value < "m" && y.size > 0, xs)) >= 2
                        then High else Low
                """;
        for (String model : List.of(alone, inARecord)) {
            List<List<String>> offered = containersOffered(model);
            assertTrue(offered.stream().anyMatch(below("m", 2)), () -> "two below: " + offered);
            assertTrue(offered.stream().noneMatch(values -> values.contains("")),
                    () -> "no label the type refuses: " + offered);
        }
    }

    /** Two counts over one list are one list: a twice and b three times. */
    @Test
    void twoCountsOfOneListAreComposedInOneList() {
        List<List<String>> offered = containersOffered("""
                module probe
                data Low
                data High
                behavior pick : (xs: List<String>) -> Low | High
                let pick (xs) =
                    if List.length(List.filter(y -> y == "a", xs)) == 2
                            && List.length(List.filter(y -> y == "b", xs)) == 3
                        then High else Low
                """);
        assertTrue(offered.stream().anyMatch(holding("a", 2).and(holding("b", 3))),
                () -> "a twice and b three times: " + offered);
    }

    /** A set holds each string once. */
    @Test
    void aSetIsComposedOfDifferentStrings() {
        List<List<String>> offered = containersOffered("""
                module probe
                data Low
                data High
                behavior pick : (xs: Set<String>) -> Low | High
                let pick (xs) =
                    if Set.size(Set.filter(y -> y == "a" || y == "b", xs)) >= 2 then High else Low
                """);
        assertTrue(offered.stream().anyMatch(holding("a", 1).and(holding("b", 1))),
                () -> "a and b: " + offered);
        offered.forEach(values -> assertEquals(new HashSet<>(values).size(), values.size(),
                () -> "a set holds each value once: " + values));
    }

    /**
     * Against another string of the input, an element is held level with the value the row holds
     * there: one dropped from what equals {@code u} leaves something only where two did, and a row
     * is composed below that line and on it.
     */
    @Test
    void aCountOfWhatEqualsAnotherStringIsComposedAgainstTheValueTheRowHoldsThere() {
        List<RowAgainstAString> offered = rowsAgainstAString("""
                module probe
                data Low
                data High
                behavior pick : (xs: List<String>, u: String) -> Low | High
                let pick (xs, u) =
                    if List.length(List.drop(1, List.filter(y -> y == u, xs))) >= 1 then High else Low
                """);
        assertTrue(offered.stream().anyMatch(row -> row.equalToIt() == 1),
                () -> "one below the line: " + offered);
        assertTrue(offered.stream().anyMatch(row -> row.equalToIt() == 2),
                () -> "one on the line: " + offered);
    }

    private static Predicate<List<String>> holding(String value, int times) {
        return values -> values.stream().filter(value::equals).count() == times;
    }

    private static Predicate<List<String>> below(String than, int times) {
        return values -> values.stream().filter(each -> each.compareTo(than) < 0).count() == times;
    }

    /** The values of every container the rows offered for {@code source} write. */
    private static List<List<String>> containersOffered(String source) {
        List<List<String>> out = new ArrayList<>();
        Matcher written = Pattern.compile("\\[([^\\]]*)\\]").matcher(rowsOffered(source));
        while (written.find()) {
            out.add(stringsIn(written.group(1)));
        }
        return out;
    }

    /** A row of a list and the string it is held against. */
    private record RowAgainstAString(List<String> values, String against) {

        long equalToIt() {
            return values.stream().filter(against::equals).count();
        }
    }

    /** Every row offered for {@code source} whose arguments are a list and then one string. */
    private static List<RowAgainstAString> rowsAgainstAString(String source) {
        List<RowAgainstAString> out = new ArrayList<>();
        Matcher written = Pattern.compile("\\| \\(\\[([^\\]]*)\\], (\"(?:[^\"\\\\]|\\\\.)*\")\\)")
                .matcher(rowsOffered(source));
        while (written.find()) {
            out.add(new RowAgainstAString(stringsIn(written.group(1)),
                    stringsIn(written.group(2)).getFirst()));
        }
        return out;
    }

    private static String rowsOffered(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return GeneratedRows.of(compilation, "probe", null,
                SourceRendering.namedByIdentity(SourceLayouts.NONE)).text();
    }

    private static List<String> stringsIn(String written) {
        List<String> values = new ArrayList<>();
        Matcher each = Pattern.compile("\"((?:[^\"\\\\]|\\\\.)*)\"").matcher(written);
        while (each.find()) {
            values.add(each.group(1));
        }
        return values;
    }
}
