package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A count of the elements meeting a statement that reads a number an operation answers of an
 * element, beside the element's own value, places each of them on the order it is a number of:
 * the length of a string is counted by one, and the string is a value of the order of strings.
 */
class ACountOfElementsMeetingANumberAnOperationAnswersPlacesThatNumberOnItsOwnOrderTest {

    @Test
    void aLengthAndAValueOfOneElementAreEachPlacedOnTheirOwn() {
        Compilation compilation = Compilation.ofSource("""
                module example.popular

                behavior popular : (xs: List<String>, label: String) -> Bool

                let popular (xs, label) =
                    List.length(List.filter(x -> String.length(x) >= 2,
                        List.filter(x -> x == label, xs))) >= 3
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList());
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        assertTrue(report.contains("#xs [String.length(xs[*]) >= 2 && label - xs[*] == 0]"),
                () -> report);
    }
}
