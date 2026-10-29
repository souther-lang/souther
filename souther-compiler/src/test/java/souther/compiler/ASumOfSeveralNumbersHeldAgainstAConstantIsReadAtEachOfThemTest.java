package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * A sum of several numbers held against a constant is read at each of them, however many there
 * are.
 *
 * <p>With the numbers of {@code Int}, the greatest value of one of them has a row that holds the
 * relation and a row that fails it: {@code a} the greatest, {@code b} the least and {@code c} a
 * hundred fails {@code a + b + c > 100}, and its sums along the way are minus one and ninety-nine.
 * Which rows a program computes is the order it adds in, and the form says none, so the number is
 * left undivided at every place where the others are shown to take the relation either way
 * whatever the order, as two numbers are and as three or more were not.
 */
class ASumOfSeveralNumbersHeldAgainstAConstantIsReadAtEachOfThemTest {

    private static final String PREAMBLE = """
            module p
            data Month = { pay: Int, days: Int }
            data Win = { a: Month, b: Month, c: Month, d: Month }
            data Ok
            data No

            behavior f : (w: Win) -> Ok | No
            """;

    private static final List<String> PLACES = List.of("w.a.pay", "w.b.pay", "w.c.pay", "w.d.pay");

    /** The places the report says nothing is read of, for a guard on {@code condition}. */
    private static List<String> unread(String condition) {
        Compilation compilation = Compilation.ofSource(PREAMBLE + """
                let f (w) = {
                    guard %s else No
                    Ok
                }
                """.formatted(condition), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .filter(line -> line.contains("not read:"))
                .map(line -> line.replaceAll(".*about `([^`]*)`.*", "$1"))
                .toList();
    }

    private static String sum(int numbers, String sign) {
        return PLACES.subList(0, numbers).stream().collect(Collectors.joining(" " + sign + " "));
    }

    @Test
    void twoOrMoreNumbersAddedAreReadAtEachOfThem() {
        for (int numbers = 2; numbers <= 4; numbers++) {
            assertEquals(List.of(), unread(sum(numbers, "+") + " >= 100"),
                    numbers + " numbers added");
        }
    }

    @Test
    void everyOrderOfTheComparisonIsReadAlike() {
        for (String order : List.of(">=", ">", "<=", "<")) {
            assertEquals(List.of(), unread(sum(3, "+") + " " + order + " 100"), order);
        }
    }

    @Test
    void aConstantAtNoughtOrBelowIsReadAlike() {
        assertEquals(List.of(), unread(sum(3, "+") + " >= 0"), "at nought");
        assertEquals(List.of(), unread(sum(3, "+") + " >= -100"), "below nought");
    }

    @Test
    void anAverageOfSeveralNumbersIsReadAtEachOfThem() {
        for (int numbers = 2; numbers <= 3; numbers++) {
            assertEquals(List.of(),
                    unread("Rational.toInt(DOWN, (" + sum(numbers, "+") + ") / " + numbers
                            + ") >= 100"),
                    numbers + " numbers averaged");
        }
    }

    /**
     * Divided by how many a list written out holds, the average is read the same: the count is no
     * number the arithmetic reads, but building the list is all the call does, and the elements
     * are worked out where the list is built.
     */
    @Test
    void anAverageDividedByTheLengthOfAListIsReadAtEachOfTheNumbers() {
        assertEquals(List.of(), unread("Rational.toInt(DOWN, ("
                + sum(3, "+") + ") / List.length([ w.a, w.b, w.c ])) >= 100"));
    }

    /** The list is built before it is counted, so an element that may stop a run is told. */
    @Test
    void anElementOfTheListThatMayStopARunIsNotLeftOutByCountingIt() {
        assertNotEquals(List.of(), unread("Rational.toInt(DOWN, ("
                + sum(3, "+") + ") / List.length([ w.a.pay + 9223372036854775807, w.b.pay,"
                + " w.c.pay ])) >= 100"));
    }

    @Test
    void aNumberTakenAwayIsReadAlike() {
        assertEquals(List.of(), unread("w.a.pay + w.b.pay - w.c.pay >= 100"), "one taken away");
        assertEquals(List.of(), unread("w.a.pay - w.b.pay - w.c.pay >= 100"), "two taken away");
    }
}
