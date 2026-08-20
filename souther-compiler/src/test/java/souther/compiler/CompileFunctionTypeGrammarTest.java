package souther.compiler;

import souther.compiler.diag.msg.ParseMessage;
import souther.compiler.diag.msg.DataMessage;
import souther.compiler.cst.CstLexer;
import souther.compiler.cst.GreenToken;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.fmt.Formatter;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;
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
    void aFunctionMayTakeAFunctionAndReturnOne() throws Exception {
        BytesClassLoader loader =
                new BytesClassLoader(Compiler.compile(NESTED), getClass().getClassLoader());
        Object check = Emitted.behavior(loader, "demo", "check").getDeclaredConstructor().newInstance();
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
        assertInstanceOf(DataMessage.NoCodecCanBeDerived.class, d.said());
    }

    // `T?` is `Option<T>` for whatever T is. Where `?` may be written is a rule of its own, and it is
    // that rule the report names — not one about functions, which would put back the asymmetry this
    // change removes: two spellings of one type, accepted by which of the two was written.
    @Test
    void anOptionalFunctionTypeIsRefusedByTheRuleAboutOptionals() {
        Diagnostic d = diagnosticOf("""
                module demo
                data R = { n: Int }
                behavior run : (v: Int) -> R
                    constructs R
                let run (v) = {
                    let p: ((Int) -> Bool)? = None
                    R { n = v }
                }
                """);
        assertInstanceOf(ParseMessage.AnOptionalIsOnlyWrittenOnAFieldOrInTheCore.class, d.said());
    }

    // On a data field, where `?` may be written, the function inside it is what the boundary refuses.
    @Test
    void anOptionalFunctionFieldIsRefusedByTheBoundary() {
        Diagnostic d = diagnosticOf("""
                module demo
                data R = { f: ((Int) -> Bool)? }
                """);
        assertInstanceOf(DataMessage.NoCodecCanBeDerived.class, d.said());
    }
}
