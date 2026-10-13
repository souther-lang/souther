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

    /**
     * The pattern tested on the outer character draws no line on the inner string; tested on the
     * inner character, the same shape draws one there.
     */
    @Test
    void aCharacterOfOneStringIsNotTakenForACharacterOfAnother() {
        String nested = """
                module p
                behavior f : (a: String, b: String) -> Int
                let f (a, b) =
                    if List.any(c -> List.any(d -> String.matches("[x]", %s), String.characters(b)),
                        String.characters(a)) then 1 else 0
                """;
        String ofTheOuter = measured(nested.formatted("c"));
        assertTrue(ofTheOuter.contains("not read"), ofTheOuter);
        assertFalse(ofTheOuter.contains("(b): "), ofTheOuter);
        String ofTheInner = measured(nested.formatted("d"));
        assertTrue(ofTheInner.contains("read as f/#(one of {0078})(b): = 1"), ofTheInner);
    }

    /**
     * Two statements about some character read one after the other are each about their own
     * string's character, though neither is read inside the other.
     */
    @Test
    void twoStatementsReadInTurnAreEachAboutTheirOwnString() {
        String report = measured("""
                module p
                behavior f : (a: String, b: String) -> Int
                let f (a, b) =
                    if List.any(c -> String.matches("[x]", c), String.characters(a))
                        && List.any(d -> String.matches("[y]", d), String.characters(b))
                    then 1 else 0
                """);
        assertTrue(report.contains("read as f/#(one of {0078})(a): = 1"), report);
        assertTrue(report.contains("read as f/#(one of {0079})(b): = 1"), report);
        assertFalse(report.contains("{0078})(b)"), report);
        assertFalse(report.contains("{0079})(a)"), report);
    }
}
