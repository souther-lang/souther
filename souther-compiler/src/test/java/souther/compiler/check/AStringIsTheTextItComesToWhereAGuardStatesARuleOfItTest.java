package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A guard's text is the text it comes to, however it is spelled.
 *
 * <p>A rule about a string states it of a text, and a guard settles the rule a clause owes when the
 * two state one rule of one value. Which rule is a question about what the text is and not about how
 * it was written down: {@code "J" ++ "P"}, a field holding {@code "JP"} and the literal are one text,
 * and the reading of an input already takes them as one. So the discharge does too.
 *
 * <p>What is not written down stays owed. A text an input supplies is no text this can work out, a
 * different text states a different rule, and a guard of another value states nothing of this one.
 */
class AStringIsTheTextItComesToWhereAGuardStatesARuleOfItTest {

    private static List<String> codesOf(String module) {
        return Compiler.compileWithWarnings(module).warnings().stream()
                .map(Diagnostic::code)
                .toList();
    }

    private static final String TYPES = """
            module demo
            data Code = String
                invariant jp = String.startsWith("JP", value)
            data Prefix = { p: String }
            data Nested = { inner: Prefix }
            """;

    /** {@code f} building a {@code Code} out of {@code s} where {@code TEXT} is what it starts with. */
    private static String guardedBy(String text) {
        return TYPES + """
                behavior f : (s: String) -> Code
                    constructs Code
                let f (s) = if String.startsWith(TEXT, s) then Code(s) else Code("JP")
                """.replace("TEXT", text);
    }

    @Test
    void theLiteral() {
        assertEquals(List.of(), codesOf(guardedBy("\"JP\"")));
    }

    @Test
    void aNameGivenIt() {
        assertEquals(List.of(), codesOf(guardedBy("jp") + """
                let jp = "JP"
                """));
    }

    @Test
    void textItFoldsTo() {
        assertEquals(List.of(), codesOf(guardedBy("\"J\" ++ \"P\"")));
    }

    @Test
    void aFieldHoldingIt() {
        assertEquals(List.of(), codesOf(guardedBy("jp.p") + """
                let jp = Prefix { p = "JP" }
                """));
    }

    @Test
    void aFieldTwoDownUnderANameGivenAName() {
        assertEquals(List.of(), codesOf(guardedBy("held.inner.p") + """
                let head = "J"
                let jp = Prefix { p = head ++ "P" }
                let held = Nested { inner = jp }
                """));
    }

    @Test
    void aLocalNameGivenWhatAFieldFoldsTo() {
        assertEquals(List.of(), codesOf(TYPES + """
                behavior f : (s: String) -> Code
                    constructs Code, Prefix
                let f (s) = {
                    let jp = Prefix { p = "J" ++ "P" }
                    let text = jp.p
                    if String.startsWith(text, s) then Code(s) else Code("JP")
                }
                """));
    }

    @Test
    void aTextAnInputSupplies() {
        assertEquals(List.of("E2011"), codesOf(TYPES + """
                behavior f : (p: String, s: String) -> Code
                    constructs Code
                let f (p, s) = if String.startsWith(p, s) then Code(s) else Code("JP")
                """));
    }

    @Test
    void anotherText() {
        assertEquals(List.of("E2011"), codesOf(guardedBy("\"U\" ++ \"S\"")));
    }

    /**
     * A guard that came out false states the rule does not hold, which is a value the clause
     * rejects — and that is so of the folded spelling exactly as it is of the literal.
     */
    @Test
    void aGuardThatCameOutFalse() {
        String falseUnder = TYPES + """
                behavior f : (s: String) -> Code
                    constructs Code
                let f (s) = if String.startsWith(TEXT, s) then Code("JP") else Code(s)
                """;
        String literal = refusalOf(falseUnder.replace("TEXT", "\"JP\""));
        assertEquals("E2010", literal);
        assertEquals(literal, refusalOf(falseUnder.replace("TEXT", "\"J\" ++ \"P\"")));
    }

    private static String refusalOf(String module) {
        return assertThrows(CompileException.class, () -> Compiler.compileWithWarnings(module))
                .code();
    }

    @Test
    void theRuleOfAnotherValue() {
        assertEquals(List.of("E2011"), codesOf(TYPES + """
                behavior f : (s: String, t: String) -> Code
                    constructs Code
                let f (s, t) = if String.startsWith("J" ++ "P", t) then Code(s) else Code("JP")
                """));
    }
}
