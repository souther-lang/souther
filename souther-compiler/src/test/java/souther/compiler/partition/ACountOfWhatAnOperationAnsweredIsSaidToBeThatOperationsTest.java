package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many code points of a class a string holds is not read where the string is what an operation
 * answered and no law of that operation says the count, and the reason names that operation: it is
 * where the reading stopped, and what a law would have to be written for.
 *
 * <p>Asked through two readers that come to such a count — the pieces of a split, and whether a
 * trimmed string holds something — so the reason is the count's own wherever it is asked, and no
 * reader puts another in its place.
 */
class ACountOfWhatAnOperationAnsweredIsSaidToBeThatOperationsTest {

    private static String model(String condition) {
        return """
                module example.counts

                data Yes
                data No

                behavior g : (email: String) -> Yes | No
                let g (email) = {
                    guard %s else No
                    Yes
                }
                """.formatted(condition);
    }

    /** The pieces of a split at one code point, of a string a case mapping wrote. */
    @Test
    void thePiecesOfALowercasedStringNameTheCaseMapping() {
        assertStoppedAt(model("List.length(String.split(\"@\", String.lowercase(email))) >= 2"),
                "String.lowercase");
    }

    /** Whether what is left of a string put together holds something, once trimmed. */
    @Test
    void aTrimmedStringPutTogetherNamesWhatPutItTogether() {
        assertStoppedAt(model("Bool.not(String.isEmpty(String.trim(String.append(email, \"x\"))))"),
                "String.append");
    }

    private static void assertStoppedAt(String model, String operation) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String report = AdequacyReport.of(compilation).human(
                SourceRendering.namedByIdentity(compilation.texts()));
        assertTrue(report.contains("how many code points of a class what " + operation
                + " answers holds"), report);
    }
}
