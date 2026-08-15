package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row spreads a value another module published, the same way it spreads one of its own.
 *
 * <p>A published value crosses closed, so spreading it is reading fields off a value already resolved —
 * which is what the language already allows in a body. Only the fixture reader refused it, and for a
 * reason that had nothing to do with the module boundary: it looked the value up by the name it was
 * *declared* under, while the values a fixture may name are keyed by how the row spells them, an imported
 * one under its module's name. So a row could name a published value but not vary a field of it
 * (issue #212).
 */
class ExampleImportedSpreadTest {

    private static final String UP = """
            module up exposing ( Deal, Wide, Small, Big, standard )

            data Deal  = { n: Int, amount: Int }
            data Small = { amount: Int }
            data Big   = { amount: Int }
            data Wide  = Small | Big

            let standard = Deal { n = 1, amount = 100 }
            """;

    @Test
    void aRowVariesAFieldOfAPublishedValue() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(UP, """
                module down
                import up ( Deal, standard )

                data Out = { m: Int }

                behavior run : (d: Deal) -> Out
                    constructs Out

                let run (d) = Out { m = d.amount }

                example run
                    | "named unchanged" : (standard) -> Out { m = 100 }
                    | "one field varied" : (Deal { ...standard, amount = 200 }) -> Out { m = 200 }
                """)));
    }

    @Test
    void anImportedValueIsSpreadInEveryPositionAFixtureIsWritten() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(UP, """
                module down
                import up ( Deal, standard )

                data Out = { m: Int }

                behavior rateOf : (d: Deal) -> Deal

                behavior run : (d: Deal) -> Out
                    depends on rateOf
                    constructs Out

                let run (d, rateOf) = Out { m = rateOf(d).amount }

                behavior echo : (d: Deal) -> Deal
                let echo (d) = d

                fake rateOf
                    | _ -> Deal { ...standard, amount = 300 }

                example run
                    | "a fake row spreads it" : (Deal { ...standard }) -> Out { m = 300 }

                example echo
                    | "the expected side spreads it"
                        : (Deal { ...standard, amount = 400 }) -> Deal { ...standard, amount = 400 }
                """)));
    }

    @Test
    void aSpreadOfAPublishedValueKeepsTheCaseTheConstructionWrites() {
        // With issue #206: the case comes from the construction, and the fields from the value — across
        // the module boundary as within one.
        assertDoesNotThrow(() -> Compiler.compileModules(List.of(UP, """
                module down
                import up ( Wide, Small, Big, standard )

                data Answer = { label: String }

                behavior labelOf : (w: Wide) -> Answer
                    constructs Answer

                let labelOf (w) =
                    match w with
                        | Small -> Answer { label = "small" }
                        | Big   -> Answer { label = "big" }

                example labelOf
                    | "a published value spread into a union position"
                        : (Big { ...standard }) -> Answer { label = "big" }
                """)));
    }

    @Test
    void aSpreadOfAPublishedValueStillHasToHold() {
        CompileException e = assertThrows(CompileException.class,
                () -> Compiler.compileModules(List.of(UP, """
                        module down
                        import up ( Deal, standard )

                        data Out = { m: Int }

                        behavior run : (d: Deal) -> Out
                            constructs Out

                        let run (d) = Out { m = d.amount }

                        example run
                            | "wrong" : (Deal { ...standard, amount = 200 }) -> Out { m = 100 }
                        """)));
        assertEquals("E1905", e.diagnostic().code());
    }

    @Test
    void aNameNoValueDenotesIsStillNotSomethingToSpread() {
        // The lookup key changed; what a fixture may spread did not.
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module solo

                data Deal = { n: Int, amount: Int }
                data Out  = { m: Int }

                behavior run : (d: Deal) -> Out
                    constructs Out

                let run (d) = Out { m = d.amount }

                let notAValue (n: Int): Int = n

                example run
                    | "a helper is not a value" : (Deal { ...notAValue, amount = 1 }) -> Out { m = 1 }
                """));
        assertEquals("E1024", e.diagnostic().code());
        assertTrue(e.getMessage().contains("is a function, and cannot be held as a value here"),
                e.getMessage());
    }
}
