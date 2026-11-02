package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A fork testing whether some piece of a string is a value is stated by the comparison of one
 * piece with that value, and states nothing of its own about the string it walks.
 *
 * <p>That holds only where the truth proved that the value is one of the pieces. Some piece being
 * another value is not the denial of that, nor a statement the comparison of a piece with the
 * value draws its relation from, so the fork over it keeps the question about the string.
 */
class TheContainerOfSomePieceEqualToAValueIsStatedByTheComparisonTest {

    private static List<String> forks(String condition) {
        Compilation compilation = Compilation.ofSource("""
                module w2
                data A
                data B
                behavior m : (email: String, d: String) -> A | B
                let m (email, d) = if %s then A else B
                """.formatted(condition), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts())).lines()
                .map(String::strip).filter(line -> line.startsWith("· not read: fork"))
                .distinct().toList();
    }

    @Test
    void somePieceBeingTheValueLeavesTheForkNothingToState() {
        assertEquals(List.of(), forks("List.any(p -> p == d, String.split(\"@\", email))"));
    }

    @Test
    void somePieceBeingTheValueInTheFirstPiecesLeavesTheForkNothingToState() {
        assertEquals(List.of(),
                forks("List.any(p -> p == d, List.take(1, String.split(\"@\", email)))"));
    }

    @Test
    void somePieceBeingAnotherValueKeepsTheQuestionAboutTheString() {
        List<String> out = forks("List.any(p -> p /= d, String.split(\"@\", email))");
        assertEquals(1, out.size(), out.toString());
    }

    @Test
    void somePieceBeingTheValueFromALaterPieceLeavesTheForkNothingToState() {
        assertEquals(List.of(),
                forks("List.any(p -> p == d, List.drop(1, String.split(\"@\", email)))"));
    }

    @Test
    void somePieceOfNoPieceLeavesTheForkNothingToState() {
        assertEquals(List.of(),
                forks("List.any(p -> p == d, List.take(0, String.split(\"@\", email)))"));
    }

    @Test
    void somePieceBeingTheStringItselfKeepsTheQuestionAboutTheString() {
        List<String> out = forks("List.any(p -> p == email, String.split(\"@\", email))");
        assertEquals(1, out.size(), out.toString());
    }
}
