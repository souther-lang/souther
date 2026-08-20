package souther.compiler.check;

import souther.compiler.source.SourceId;

import souther.compiler.Compiler;
import souther.compiler.diag.msg.MessageKeys;
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
        Map<SourceId, List<Located>> found = Compiler.diagnoseModules(Map.of("demo", """
                module demo

                %s
                %s
                """.formatted(NOWHERE, body)));
        return found.getOrDefault(new SourceId("demo"), List.of()).stream()
                .map(l -> MessageKeys.of(l.diagnostic().said())).toList();
    }

    @Test
    void theOperandBesideOneThatFailedDoesNotCoverIt() {
        List<String> keys = messageKeys("""
                behavior f : (a: A) -> Int
                let f (a) = ("x" ++ 1) + a.n
                """);

        assertTrue(keys.contains("type.joins-two-lists-or-two-strings"),
                "the operand that said what was wrong with it is reported: " + keys);
    }

    /**
     * `&&` and `||` are the operators that ask something of an operand on its own, so an operand
     * they refuse has failed where it stands and the operand beside it is not reached. The rest ask
     * about the pair, and cannot answer until both have been read.
     */
    @Test
    void anOperandTheOperatorRefusesOnItsOwnComesBeforeWhatStandsBesideIt() {
        List<String> keys = messageKeys("""
                behavior f : (a: A) -> Bool
                let f (a) = 1 && ("x" ++ 1)
                """);

        assertTrue(keys.contains("type.it-does-not-have-the-type-it-needs-here"),
                "`1` is not a Bool, and that is what `&&` was given first: " + keys);
        assertFalse(keys.contains("type.joins-two-lists-or-two-strings"),
                "the operand beside it was never read: " + keys);
    }

    /**
     * The same rule where what stands beside it is an operand with no type. Abandoning the
     * definition is for what follows from a name that denotes nothing, and an operand the operator
     * refuses before reaching that name does not follow from it.
     */
    @Test
    void anOperandTheOperatorRefusesIsReportedThoughTheOneBesideItHasNoType() {
        List<String> keys = messageKeys("""
                behavior f : (a: A) -> Bool
                let f (a) = 1 && a.n
                """);

        assertTrue(keys.contains("type.it-does-not-have-the-type-it-needs-here"),
                "`1` is not a Bool, whatever stands beside it: " + keys);
    }

    @Test
    void anOperandWithNoTypeStopsTheOneBesideItFromBeingRead() {
        List<String> keys = messageKeys("""
                behavior f : (a: A) -> Int
                let f (a) = a.n + ("x" ++ 1)
                """);

        assertFalse(keys.contains("type.joins-two-lists-or-two-strings"),
                "reading stopped at the operand with no type, so nothing beside it was read: " + keys);
    }

    @Test
    void anOperandWithNoTypeIsNotReportedAsTheWrongTypeForTheOperator() {
        List<String> keys = messageKeys("""
                behavior f : (a: A) -> Int
                let f (a) = 1 + a.n
                """);

        assertEquals(List.of("name.no-type-of-that-name"), keys,
                "the name that denotes nothing, and nothing about adding it: " + keys);
    }
}
