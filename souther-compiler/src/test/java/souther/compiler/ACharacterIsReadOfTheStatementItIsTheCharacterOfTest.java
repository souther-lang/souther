package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What is stated of a character is read of the statement about some character it is the character
 * of, and of no other one being read with it.
 *
 * <p>Asked of the report a person reads: a character of one string tested inside a statement about
 * some character of another is a character of the first, so no line is drawn on the second string
 * for what the pattern accepts.
 */
class ACharacterIsReadOfTheStatementItIsTheCharacterOfTest {

    private static String measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors(), "the model compiles");
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    @Test
    void aCharacterOfOneStringIsNotTakenForACharacterOfAnother() {
        String report = measured("""
                module p
                behavior f : (a: String, b: String) -> Int
                let f (a, b) =
                    if List.any(c -> List.any(d -> String.matches("[x]", c), String.characters(b)),
                        String.characters(a)) then 1 else 0
                """);
        assertTrue(report.contains("not read"), report);
        assertFalse(report.contains("(b): "), report);
    }
}
