package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * A number taken directly of a list that holds every element of a position, each as often, is the
 * number of that position.
 *
 * <p>{@code List.reverse(xs)} and {@code List.sortBy(f, xs)} hold the elements of {@code xs} in
 * another order, and what they add up to or how many they hold does not turn on the order. So the
 * comparison is read as one of {@code xs}, the same term the comparison written of {@code xs} is.
 * What keeps some of the elements is not: {@code [4, 6]} taken two of from the back comes to six
 * where both come to ten.
 */
class ATotalOfAReorderingIsTheTotalOfWhatItReordersTest {

    private static String model(String number) {
        return """
                module probe.k1

                data Yes = { n: Int }
                data No = { n: Int }

                behavior verify : (xs: List<Int>) -> Yes | No
                    constructs Yes, No

                let verify (xs) = {
                    let ys = List.reverse(xs)
                    if %s >= 5 then Yes { n = 0 } else No { n = 0 }
                }
                """.formatted(number);
    }

    @Test
    void aTotalOfEveryElementInAnotherOrderIsTheTotalOfThePosition() {
        String asWritten = linesOf(report(model("List.sum(xs)")));
        for (String reordered : new String[] {
                "List.sum(List.reverse(xs))",
                "List.sum(List.sortBy(x -> x, xs))",
                "List.sum(List.reverse(List.sortBy(x -> x, xs)))",
                "List.sum(List.map(x -> x, List.reverse(xs)))",
                "List.sum(ys)"}) {
            assertEquals(asWritten, linesOf(report(model(reordered))), reordered);
        }
    }

    /** Control: a count was read through a reordering before a total was, and stays the count of
     *  the position. */
    @Test
    void aCountOfEveryElementInAnotherOrderIsTheCountOfThePosition() {
        assertEquals(linesOf(report(model("List.length(xs)"))),
                linesOf(report(model("List.length(List.reverse(xs))"))));
    }

    @Test
    void aTotalOfSomeOfTheElementsIsNoTotalOfThePosition() {
        String asWritten = linesOf(report(model("List.sum(xs)")));
        for (String some : new String[] {
                "List.sum(List.take(2, xs))",
                "List.sum(List.filter(x -> x > 0, xs))",
                "List.sum(List.reverse(List.filter(x -> x > 0, xs)))",
                "List.sum(List.map(x -> 2 * x, List.reverse(xs)))"}) {
            String report = report(model(some));
            assertNotEquals(asWritten, linesOf(report),
                    some + "\n" + report);
        }
    }

    /** What the report says of the comparison, with where it stands in the source left out. */
    private static String linesOf(String report) {
        return report.replaceAll("\\d+:\\d+", "");
    }

    private static String report(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(0, compilation.errors().size(), () -> "the source compiles: " + model);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
