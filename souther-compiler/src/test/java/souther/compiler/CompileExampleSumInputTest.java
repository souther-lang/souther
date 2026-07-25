package souther.compiler;

import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An {@code example} whose input is a sum names the case it means, the same way a body constructs one.
 * The verifier builds the fixture through the decoder that reads it, and a sum's decoder dispatches on
 * a discriminator — so the tag the fixture never writes is added here. Without it, a behavior taking a
 * sum could not be examined at all: every row failed to build its input.
 */
class CompileExampleSumInputTest {

    private static final String MODULE = """
            module demo

            data 現金 = { 金額: Int }
            data 振込 = { 口座: String }
            data 未定

            data 支払 = 現金 | 振込 | 未定

            data 判定 = { 即時: Bool }

            behavior 即時か : (支払: 支払) -> 判定 constructs 判定

            let 即時か (支払) =
                match 支払 with
                    | 現金 { 金額 } -> 判定 { 即時 = 金額 >= 0 }
                    | 振込 { 口座 } -> 判定 { 即時 = false }
                    | 未定          -> 判定 { 即時 = false }

            example 即時か
                | "現金は即時" : (現金 { 金額 = 500 }) -> 判定 { 即時 = true }
                | "振込は即時ではない" : (振込 { 口座 = "1234567" }) -> 判定 { 即時 = false }
                | "値を持たないケースも書ける" : (未定) -> 判定 { 即時 = false }
            """;

    @Test
    void aFixtureNamesTheCaseForASumTypedInput() {
        assertDoesNotThrow(() -> Compiler.compile(MODULE));
    }

    @Test
    void aFieldTheFixtureWroteIsNotReplacedByTheTag() {
        // A case whose own field is named like its sum's discriminator is already ambiguous at the
        // boundary. The fixture's value stays, so the row fails on the tag it cannot match instead of
        // passing while decoding something the author did not write.
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile("""
                module demo

                data A = { type: String, n: Int }
                data B = { m: Int }
                data S = A | B
                data Out = { v: Int }

                behavior run : (s: S) -> Out constructs Out

                let run (s) =
                    match s with
                        | A { n } -> Out { v = n }
                        | B { m } -> Out { v = m }

                example run
                    | "the written `type` is what is decoded" : (A { type = "wat", n = 7 })
                        -> Out { v = 7 }
                """));
        assertTrue(e.getMessage().contains("A") && e.getMessage().contains("B"), e.getMessage());
    }

    @Test
    void theExampleStillHasToHold() {
        // The tagging is not a way past the check: a wrong expectation fails as any other row does.
        assertThrows(CompileException.class, () -> Compiler.compile(
                MODULE.replace("\"現金は即時\" : (現金 { 金額 = 500 }) -> 判定 { 即時 = true }",
                        "\"現金は即時\" : (現金 { 金額 = 500 }) -> 判定 { 即時 = false }")));
    }
}
