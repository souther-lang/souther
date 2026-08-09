package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.diag.Located;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An operator reads its operands left to right and reports the first one that failed.
 *
 * <p>An operand whose type the compiler could not work out gives the operator no shape to check
 * against, so the definition is abandoned rather than told what {@code ?} is not. That is about the
 * operand it is read from: an operand of its own that already said what was wrong with it has been
 * reported, and the operand beside it does not take that back.
 */
class TheOperandThatFailedFirstIsTheOneReportedTest {

    /** `n` is declared at a type nothing declares, so `a.n` is the type the compiler could not work
     *  out; `"x" ++ 1` is an operand that says what is wrong with it. */
    private static final String NOWHERE = """
            data A = { n: Nowhere }
            """;

    private static List<String> messageKeys(String body) {
        Map<String, List<Located>> found = Compiler.diagnoseModules(Map.of("demo", """
                module demo

                %s
                %s
                """.formatted(NOWHERE, body)));
        return found.getOrDefault("demo", List.of()).stream()
                .map(l -> l.diagnostic().messageKey()).toList();
    }

    @Test
    void theOperandBesideOneThatFailedDoesNotCoverIt() {
        List<String> keys = messageKeys("""
                behavior f : (a: A) -> Int
                let f (a) = ("x" ++ 1) + a.n
                """);

        assertTrue(keys.contains("check.concat.msg"),
                "the operand that said what was wrong with it is reported: " + keys);
    }

    @Test
    void anOperandWithNoTypeStopsTheOneBesideItFromBeingRead() {
        List<String> keys = messageKeys("""
                behavior f : (a: A) -> Int
                let f (a) = a.n + ("x" ++ 1)
                """);

        assertFalse(keys.contains("check.concat.msg"),
                "reading stopped at the operand with no type, so nothing beside it was read: " + keys);
    }

    @Test
    void anOperandWithNoTypeIsNotReportedAsTheWrongTypeForTheOperator() {
        List<String> keys = messageKeys("""
                behavior f : (a: A) -> Int
                let f (a) = 1 + a.n
                """);

        assertEquals(List.of("check.unknown.type.msg"), keys,
                "the name that denotes nothing, and nothing about adding it: " + keys);
    }
}
