package souther.compiler;

import souther.compiler.cst.CstLexer;
import souther.compiler.cst.GreenToken;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.fmt.Formatter;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A function type's parameters and result are whole types, so it nests: a function may take one and
 * return one, and a collection may hold one. The formatter reads back what the grammar admits — a
 * type it cannot see is a type it drops.
 */
class CompileFunctionTypeGrammarTest {

    private static Diagnostic diagnosticOf(String src) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(src));
        return e.diagnostic();
    }

    private static final String NESTED = """
            module demo

            data Order = { xs: List<Int> }
            data Result = { ns: List<Int> }

            let twice (g: ((Int) -> Int), v: Int) = g(g(v))

            let adder (n: Int): (Int) -> Int = (x) -> x + n

            behavior check : (o: Order) -> Result
                constructs Result

            let check (o) = {
                let bump: (Int) -> Int = adder(1)
                Result { ns = List.map((x) -> twice(bump, x), o.xs) }
            }
            """;

    @Test
    @SuppressWarnings("unchecked")
    void aFunctionMayTakeAFunctionAndReturnOne() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(NESTED), getClass().getClassLoader());
        Object check = loader.loadClass("demo.Check" + "$Impl").getDeclaredConstructor().newInstance();
        Object order = Codecs.decoded(loader, "demo.Order", Map.of("xs", List.of(10L, 20L)));
        assertEquals(List.of(12L, 22L),
                ((Map<?, ?>) Codecs.encode(loader, "demo.Result",
                        Codecs.apply(check, order))).get("ns"));
    }

    @Test
    void theFormatterKeepsEveryTokenOfANestedFunctionType() {
        String formatted = Formatter.format(NESTED);
        assertEquals(tokens(NESTED), tokens(formatted));
    }

    private static List<String> tokens(String src) {
        List<String> out = new java.util.ArrayList<>();
        for (GreenToken t : CstLexer.lex(src).tokens()) {
            if (!t.kind().isTrivia() && t.kind() != SyntaxKind.EOF) {
                out.add(t.kind() + ":" + t.text());
            }
        }
        return out;
    }

    // A named type is checked where it is declared, so a reference to one carries what that check
    // already settled. Reaching a function through a name does not get past the boundary.
    @Test
    void aFunctionCannotReachTheBoundaryThroughANamedType() {
        Diagnostic d = diagnosticOf("""
                module demo
                data Hidden = { f: (Int) -> Bool }
                data R = { h: Hidden }
                behavior run : (r: R) -> R
                """);
        assertEquals("check.derive.nocodec", d.messageKey());
    }
}
