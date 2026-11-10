package souther.compiler;

import souther.compiler.diag.msg.MessageKeys;
import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What E2010 says a construction was refuted <em>by</em>. The check decides a violation from two
 * kinds of fact: what the values it is handed carry on their own — a literal, an arithmetic result, a
 * name given a written value, an input's own type invariant — and what a condition on the path
 * assumed. Only the second is something a guard settled, so only the second is said that way; a
 * construction refuted without any of it is said without mentioning the path at all.
 */
class CompileInvariantViolationReasonTest {

    /** The reason of a construction the values it is handed refute, naming no path. */
    private static final String ON_THE_VALUES =
            "invariant.the-value-is-one-the-invariant-rejects-unnamed";

    /** The reason of a construction refuted only under a condition on the path. */
    private static final String ON_A_PATH =
            "invariant.the-value-is-rejected-on-a-reachable-path-unnamed";

    /** The message key E2010 was raised with, which is what the reason is chosen by. */
    private static String reasonOf(String module) {
        CompileException e = assertThrows(CompileException.class, () -> Compiler.compile(module));
        assertEquals("E2010", e.diagnostic().code(), e.getMessage());
        return MessageKeys.of(e.diagnostic().said());
    }

    /** A module, and why the reason it gets is the one the table says. */
    private record Refuted(String why, String module) {
    }

    /** An invariant is the conjunction of its clauses, so one clause failing on the values alone is
     * the whole invariant failing on them — whatever the other clauses needed to fail. */
    private static final String TWO_CLAUSES = """
            module demo
            data Pair = { x: Int, y: Int }
            %s
            behavior mk : (x: Int) -> Pair constructs Pair
            let mk (x) =
                if x < 0 then Pair { x = x, y = 0 - 1 }
                else Pair { x = 0, y = 0 }
            """;

    /**
     * Nothing a guard settled is what refutes these, so the reason mentions no path: the values
     * written decide it, or what an input's own type carries wherever the input goes.
     */
    @Test
    void aConstructionTheValuesAloneRefuteIsRefutedWithoutAnyPath() {
        List<Refuted> cases = List.of(
                new Refuted("nothing is guarded here — the values written decide it", """
                        module demo
                        data Range = { lo: Int, hi: Int }
                            invariant lo <= hi
                        behavior mk : () -> Range constructs Range
                        let mk = Range { lo = 5, hi = 1 }
                        """),
                new Refuted("0 - 1 is negative wherever it stands", """
                        module demo
                        data Money = Decimal
                            invariant value >= 0m
                        behavior calc : (m: Money) -> Money constructs Money
                        let calc (m) = Money(0m) - Money(1m)
                        """),
                // `p.value > 0` is what Pos guarantees of its value, not what a guard settled
                new Refuted("an input's type carries its invariant everywhere the input does", """
                        module demo
                        data Pos = Int
                            invariant value > 0
                        data Neg = Int
                            invariant value < 0
                        behavior conv : (p: Pos) -> Neg constructs Neg
                        let conv (p) = Neg(p.value)
                        """),
                new Refuted("a name is an alias for what it was given, and no guard was written", """
                        module demo
                        data Amount = Int
                            invariant value >= 0
                        behavior mk : (n: Int) -> Amount constructs Amount
                        let mk (n) = {
                            let bad = 0 - 5
                            Amount(bad)
                        }
                        """),
                new Refuted("the guard settles something, and the violation does not need it", """
                        module demo
                        data Money = Decimal
                            invariant value >= 0m
                        data Pair = { a: Money, b: Money }
                        behavior pick : (p: Pair) -> Money constructs Money
                        let pick (p) =
                            if p.a < p.b then Money(0m) - Money(1m)
                            else p.a
                        """),
                // `x >= 0` fails only under the guard; `y >= 0` fails on `y = -1` wherever it is
                // written, so the invariant is already false without the guard by its second clause
                new Refuted("one clause refuted on the values alone decides the whole invariant",
                        TWO_CLAUSES.formatted("    invariant x >= 0\n    invariant y >= 0")),
                new Refuted("the same two clauses in the other order are the same invariant",
                        TWO_CLAUSES.formatted("    invariant y >= 0\n    invariant x >= 0")));
        for (Refuted each : cases) {
            assertEquals(ON_THE_VALUES, reasonOf(each.module()), each.why());
        }
    }

    /**
     * What a guard forces is said as an assumption: without {@code n < 0} nothing there refutes the
     * invariant. Where two readings of one construction are refuted differently it stays an error,
     * and what is claimed of the two together is what the reading that needed the path supports.
     */
    @Test
    void aConstructionOnlyAGuardRefutesIsSaidAsAnAssumption() {
        List<Refuted> cases = List.of(
                new Refuted("without `n < 0` nothing here refutes the invariant", """
                        module demo
                        data Amount = Int
                            invariant value >= 0
                        behavior mk : (n: Int) -> Amount constructs Amount
                        let mk (n) =
                            if n < 0 then Amount(n)
                            else Amount(0)
                        """),
                // read with `n`, the guard decides it; read with `0 - 1`, the value does
                new Refuted("one reading needed the path, so the two together are said to", """
                        module demo
                        data Amount = Int
                            invariant value >= 0
                        behavior mk : (n: Int) -> Amount constructs Amount
                        let mk (n) = Amount(if n < 0 then n else 0 - 1)
                        """));
        for (Refuted each : cases) {
            assertEquals(ON_A_PATH, reasonOf(each.module()), each.why());
        }
    }
}
