package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A total of what a walk answered of the elements a filter kept is not the total of every element
 * standing at the position.
 *
 * <p>A total is of every value standing there, each once, and an element the filter left out adds
 * nothing to what the program sums: {@code [4, 6]} kept by {@code q > 5} comes to six, where every
 * element comes to ten. So the walk is placed by the question a total asks of it — every
 * occurrence, each once — which a reordering answers and a filter does not.
 */
class ATotalOverSomeOfTheElementsIsNoTotalOfThemAllTest {

    private static String model(String total) {
        return """
                module p
                data Bad
                data Line = { q: Int }
                behavior check : (ls: List<Line>) -> Int | Bad
                let check (ls) = {
                    guard %s >= 10 else Bad
                    0
                }
                """.formatted(total);
    }

    /** Control: every element, in the order written or in another, is the total of them all. */
    @Test
    void everyElementInAnyOrderIsTheTotalOfThemAll() {
        for (String walked : new String[] {"ls", "List.reverse(ls)", "List.sortBy(l -> l.q, ls)"}) {
            String human = report(model("List.sum(List.map(l -> l.q, " + walked + "))"));
            assertTrue(human.contains("no line: comparison")
                    && human.contains("List.sum(ls[*].q)"), walked + "\n" + human);
        }
    }

    /** What a filter kept is some of them, and no total of them all, whatever the walk answers of
     *  each. */
    @Test
    void whatAFilterKeptIsNoTotalOfThemAll() {
        String place = report(model(
                "List.sum(List.map(l -> l.q, List.filter(l -> l.q > 5, ls)))"));
        assertFalse(place.contains("List.sum(ls[*].q)"), place);
        assertTrue(place.contains("not read: comparison"), place);
        String computed = report(model(
                "List.sum(List.map(l -> 2 * l.q, List.filter(l -> l.q > 5, ls)))"));
        assertFalse(computed.contains("| ls[*]}"), computed);
        assertTrue(computed.contains("not read: comparison"), computed);
    }

    private static String report(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
