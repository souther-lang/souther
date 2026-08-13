package souther.compiler;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import souther.compiler.diag.CompileException;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A pattern that opens a newtype names it the way a name is written anywhere else — bare when an
 * import brings it in, through its module otherwise. The layer checks used to compare the written
 * text against the type's own simple name, so the qualified spelling of the very type being opened
 * was rejected; both sides are the resolved name now (issue #177).
 */
class CompileQualifiedPatternTest {

    /**
     * A qualified case name is reported as the name it is, not as a case that was bound the wrong
     * way. The parser recognises {@code Some} by its spelling — it runs before any name means
     * anything, and {@code Some} has only the one spelling — but that recognition has no answer for
     * a qualified name, so advising {@code as} there would suggest a spelling that does not work
     * either. What is wrong is the name, which resolution says.
     */
    @Test
    void aQualifiedCaseNameIsReportedAsTheNameItIs() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compile("""
                        module app
                        data In = { a: Int? }
                        data Out = { n: Int }
                        data Missing
                        behavior go : (i: In) -> Out | Missing constructs Out, Missing
                        let go (i) = match i.a with
                            | Option.Some v -> Out { n = v }
                            | None -> Missing
                        """));
        assertTrue(e.getMessage().contains("Option"), e.getMessage());
        assertTrue(!e.getMessage().contains("bound with"), e.getMessage());
    }

    private static final String UP = """
            module up exposing ( Amount, Wrapped )

            data Amount = Int
            data Wrapped = Amount
            """;

    private static Object run(String down, Map<String, Object> input) throws Exception {
        BytesClassLoader loader = new BytesClassLoader(
                Compiler.compileModules(List.of(UP, down)), CompileQualifiedPatternTest.class.getClassLoader());
        Object b = Emitted.behavior(loader, "down", "run").getConstructor().newInstance();
        return Codecs.apply(b, Codecs.decoded(loader, "down.In", input));
    }

    @Test
    void anInnerLayerIsNamedThroughItsModule() throws Exception {
        // `up.Wrapped(up.Amount(n))`: the inner layer is written qualified, and what it opens is the
        // `Amount` that `Wrapped` wraps — the same type, however either side spells it
        Object out = run("""
                module down exposing ( In, Out, run )

                data In = { w: up.Wrapped }
                data Out = { m: Int }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = {
                    let up.Wrapped(up.Amount(n)) = i.w
                    Out { m = n }
                }
                """, Map.of("w", 7L));

        assertEquals(7L, out.getClass().getMethod("m").invoke(out));
    }

    @Test
    void theOpenedLayerMayBeQualifiedWhileTheFieldNamesTheImportedType() throws Exception {
        Object out = run("""
                module down exposing ( In, Out, run )
                import up ( Amount, Wrapped )

                data In = { w: Wrapped }
                data Out = { m: Int }

                behavior run : (i: In) -> Out constructs Out

                let run (i) = {
                    let up.Wrapped(up.Amount(n)) = i.w
                    Out { m = n }
                }
                """, Map.of("w", 3L));

        assertEquals(3L, out.getClass().getMethod("m").invoke(out));
    }

    @Test
    void anOptionsElementIsNamedThroughItsModule() throws Exception {
        // `Some(up.Amount(v))` opens the element the Option wraps; the element check compared the
        // element type's simple name against the written one, so only the bare spelling passed
        Object out = run("""
                module down exposing ( In, Out, run )

                data In = { a: up.Amount? }
                data Out = { m: Int }

                behavior run : (i: In) -> Out constructs Out

                let run (i) =
                    match i.a with
                        | Some(up.Amount(v)) -> Out { m = v }
                        | None -> Out { m = 0 }
                """, Map.of("a", 5L));

        assertEquals(5L, out.getClass().getMethod("m").invoke(out));
    }
}
