package souther.compiler;

import souther.compiler.diag.Primary;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.HumanRenderer;
import souther.compiler.diag.SourceContext;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A unit data is constructed by writing its name bare — the functional-language idiom for a
 * nullary constructor (spec §unit-data). It still needs {@code constructs} (spec §closed-construction, §constructs).
 */
class CompileUnitValueTest {

    private static final String MODULE = """
            module demo

            data Mark
            data Flag = Bool

            behavior marks : (f: Flag) -> List<Mark> constructs Mark

            let marks (f) = [Mark | f.value]
            """;

    private List<?> marks(boolean on) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(Compiler.compile(MODULE), getClass().getClassLoader());
        Object flag = Codecs.decoded(loader, "demo.Flag", on);   // Flag is a single-Bool newtype: bare bool
        return (List<?>) Codecs.apply(Emitted.behavior(loader, "demo", "marks")
                .getConstructor().newInstance(), flag);
    }

    @Test
    void bareUnitNameConstructsTheUnit() throws Exception {
        List<?> present = marks(true);
        assertEquals(1, present.size());
        assertEquals("demo.Mark", present.get(0).getClass().getName());

        assertEquals(0, marks(false).size());
    }

    @Test
    void constructingAUnitStillNeedsConstructs() {
        // constructing the unit `Mark` (a bare name) counts: `Note` is declared but `Mark` is also
        // built, so the undeclared `Mark` is E1002 (a declared `constructs` must list every build).
        String src = """
                module demo
                data Mark
                data Note
                data Flag = Bool
                behavior marks : (f: Flag) -> Mark | Note constructs Note
                let marks (f) = if f.value then Mark else Note
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertEquals("E1002", e.code());
    }

    /** A unit has no fields, so an invariant on it has nothing to observe and nothing it could
     *  reject (spec §unit-data). It has to be refused where it is written: `Ast.UnitData` has no
     *  slot for one, so anything not caught here is dropped without a word. */
    @Test
    void aUnitDataCannotCarryAnInvariant() {
        String src = """
                module demo
                data Mark
                    invariant false
                data Out = { s: String }
                behavior k : (n: Int) -> Out | Mark constructs Out, Mark
                let k (n) = if n > 0 then Out { s = "x" } else Mark
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertTrue(e.getMessage().contains("invariant"), e.getMessage());
        assertEquals(3, e.pos().line(), "must point at the clause, not the data");
    }

    /** The clause is refused before it is elaborated, so this would otherwise be accepted with an
     *  unbound name inside it — which is how the silent drop showed up. */
    @Test
    void aUnitDataInvariantIsRefusedEvenWhenItsExpressionIsNonsense() {
        String src = """
                module demo
                data Mark
                    invariant nonexistent > 0
                data Out = { s: String }
                behavior k : (n: Int) -> Out constructs Out
                let k (n) = Out { s = "x" }
                """;
        assertThrows(CompileException.class, () -> Compiler.compile(src));
    }

    /** An empty body names a type with one value, which is what a unit data is, so it is the second
     *  way to write one — and the two reject each other's construction. Only the unit form remains. */
    @Test
    void anEmptyProductBodyIsRefused() {
        String src = """
                module demo
                data Mark = {}
                data Out = { s: String }
                behavior k : (n: Int) -> Out constructs Out
                let k (n) = Out { s = "x" }
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertTrue(e.getMessage().contains("empty body"), e.getMessage());
        assertEquals(2, e.pos().line(), "must point at the body");
        assertEquals(13, e.pos().column(), "must start at the opening brace");
        String out = new HumanRenderer(false)
                .render(e.diagnostic(), new SourceContext("demo.sou", src), Locale.ENGLISH);
        assertTrue(out.contains("^^"), out);   // the whole `{}`, not just the opening brace
    }

    /** A body written open is still underlined from its opening brace: the region spans to the
     *  closing brace wherever it sits, and the renderer draws one caret across lines. */
    @Test
    void anEmptyBodySpanningLinesIsUnderlinedFromItsBrace() {
        String src = """
                module demo
                data Mark = {
                }
                data Out = { s: String }
                behavior k : (n: Int) -> Out constructs Out
                let k (n) = Out { s = "x" }
                """;
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        assertTrue(e.getMessage().contains("empty body"), e.getMessage());
        assertEquals(2, e.pos().line(), "must point at the opening brace");
        assertEquals(1, ((Primary.InSource) e.diagnostic().primary()).place().region().sourceSpan(), "a multi-line region draws one caret");
    }

    /** A spread body is a body: what it includes decides the fields, and an empty one cannot be
     *  written any more, so this stays a data with fields. */
    @Test
    void aSpreadOnlyBodyIsStillAProduct() {
        String src = """
                module demo
                data Base = { s: String }
                data Mark = { ...Base }
                behavior k : (n: Int) -> Mark constructs Mark
                let k (n) = Mark { s = "x" }
                """;
        assertDoesNotThrow(() -> Compiler.compile(src));
    }
}
