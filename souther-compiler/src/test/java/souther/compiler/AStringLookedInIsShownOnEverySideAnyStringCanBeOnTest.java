package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A string looked in, lowercased, with strings looked for that are lowercased and not empty, is
 * shown on both sides wherever it is: the empty string has none of them inside it, and no string
 * holding a letter the conversion answers in a way that depends on what stands beside it is left
 * open. What a conversion answers of a string with a code point is a string with one, so the
 * strings it may answer are not the empty string, which is only the answer of the empty string.
 */
class AStringLookedInIsShownOnEverySideAnyStringCanBeOnTest {

    @Test
    void anyStringLookedInIsShownThoughTheStringsLookedForAreAnyLowercased() {
        Compilation compilation = ACompiledModel.measured("""
                module probe

                data Yes
                data No
                data Point = String
                    invariant String.length(value) >= 1

                behavior f : (cases: List<Point>, q: String) -> Yes | No
                let f (cases, q) =
                    if List.any(p -> String.contains(String.lowercase(p.value),
                            String.lowercase(q)), cases)
                    then Yes else No
                """, Adequacy.Asked.fullReport());
        String report = AdequacyReport.of(compilation)
                .humanInEnglish(SourceRendering.namedByIdentity(compilation.texts()));

        assertFalse(report.contains("shown on neither side"), report);
    }
}
