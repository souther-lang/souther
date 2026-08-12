package souther.compiler.diag;

import souther.compiler.Compiler;
import org.junit.jupiter.api.Test;

import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/** A hint carries placeholders of its own ({@code Add `constructs {1}` to `{0}`}). A site that names
 * the hint without repeating the message's arguments used to render the placeholders verbatim, so a
 * hint with no arguments of its own takes the diagnostic's. */
class DiagnosticHintArgsTest {

    private static String render(String src) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        return new HumanRenderer(false).render(e.diagnostic(), null, Locale.ENGLISH);
    }

    private static void assertNoPlaceholder(String rendered) {
        for (int i = 0; i < 4; i++) {
            assertFalse(rendered.contains("{" + i + "}"),
                    "unsubstituted placeholder {" + i + "} in:\n" + rendered);
        }
    }

    @Test
    void anUnderDeclaredConstructsHintNamesTheCase() {
        String rendered = render("""
                module demo
                data Response = { id: String }
                data Empty
                behavior make : (x: String) -> Response | Empty constructs Empty

                let make (x) = if x == "" then Empty else Response { id = x }
                """);
        assertNoPlaceholder(rendered);
        assertTrue(rendered.contains("constructs Response"), rendered);
    }

    @Test
    void anOverDeclaredConstructsHintNamesTheCase() {
        String rendered = render("""
                module demo
                data Amount = Int
                data Line = { subtotal: Amount, shipping: Amount }
                data Total = { amount: Amount }
                behavior sum : (l: Line) -> Total constructs Total, Amount

                let sum (l) = Total { amount = l.subtotal + l.shipping }
                """);
        assertNoPlaceholder(rendered);
        assertTrue(rendered.contains("`Amount`"), rendered);
    }

    @Test
    void aMissingFieldHintNamesTheField() {
        String rendered = render("""
                module demo
                data Point = { x: Int, y: Int }
                behavior make : (n: Int) -> Point constructs Point

                let make (n) = Point { x = n }
                """);
        assertNoPlaceholder(rendered);
        assertTrue(rendered.contains("`y`"), rendered);
    }

    @Test
    void aMissingRequiresHintNamesTheDependency() {
        String rendered = render("""
                module demo
                data Id = String
                data Row = { id: Id }
                behavior load : (id: Id) -> Row constructs Row
                behavior run : (id: Id) -> Row

                let run (id) = load(id)
                """);
        assertNoPlaceholder(rendered);
        assertTrue(rendered.contains("depends on load"), rendered);
    }

    @Test
    void anUnusedRequiresHintNamesTheDependency() {
        String rendered = render("""
                module demo
                data Id = String
                data Row = { id: Id }
                behavior load : (id: Id) -> Row constructs Row
                behavior run : (id: Id) -> Row
                    constructs Row
                    depends on load

                let run (id, load) = Row { id = id }
                """);
        assertNoPlaceholder(rendered);
        assertTrue(rendered.contains("`load`"), rendered);
    }
}
