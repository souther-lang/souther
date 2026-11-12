package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * What a case conversion answers is every string it leaves as it stands, and the strings it maps
 * from the code points it is exactly a map on. A string against that answer is read over both, so
 * a place held to a string of the code points the conversion leaves is not left open for the
 * conversion's image where the other side holds every string.
 */
class AComparisonWithWhatACaseConversionAnswersIsReadOverItsImageTest {

    private static String report(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE));
    }

    private static String comparing(String body) {
        return """
                module p1

                behavior same : (a: String, b: String) -> Bool
                let same (a, b) = BODY

                example same
                    | "equal" : ("ab", "ab") -> true
                    | "differ" : ("ab", "cd") -> false
                """.replace("BODY", body);
    }

    @Test
    void aStringAgainstTheLowercaseOfAnyStringIsNotOpenForTheImage() {
        for (String body : new String[] {"String.lowercase(a) == b",
                "String.uppercase(a) == b"}) {
            String json = report(comparing(body));
            assertFalse(json.contains("\"imagesNotShown\""), () -> body + " " + json);
            // Nothing is left unanswered for either place: the classes cover every value.
            assertFalse(json.contains("regionNotDetermined"), () -> body + " " + json);
            assertFalse(json.contains("relation_shown_over_a_region"), () -> body + " " + json);
        }
    }
}
