package souther.compiler;

import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What an evaluation guarantees holds after it has answered, and not before.
 *
 * <p>A call carries what its behavior declared of every answer it gives, and a construction reached
 * after it is judged under that. Reaching it is the condition: the guarantee is about a value that
 * evaluation produced, and where the evaluation has not run there is no such value. A declaration
 * the body could not prove is the plain case — the run-time check stands for it, so a caller that
 * came back from the call may assume it and a caller that has not reached the call may not — but
 * nothing here rests on that. An evaluation that aborts never answers at all, and what it would
 * have guaranteed is then a fact about nothing whether or not its body proved it.
 *
 * <p>The reading used to be taken over the whole of a region before any of it was walked, so a
 * guarantee stood wherever the region did. Since what a call guarantees constrains the arguments it
 * relates its answer to, a construction written in an argument was being discharged by what the call
 * around it promises about the answer that argument has not yet produced, and a construction in one
 * field by what the field after it answers. Facts ran backwards through the evaluation.
 *
 * <p>Two directions, because there are two ways for an evaluation to stand after another: beside it
 * and above it. A later sibling is the first; the call an argument is written in is the second.
 *
 * <p>Silence is not what either is read off. Every source here reports the construction inside
 * {@code tagged}, which is one the check cannot discharge and never could — so a reading that never
 * ran would be visible as that count dropping rather than as a quiet pass. What the property is read
 * off is the second report appearing exactly where the guarantee has not run yet, against the same
 * program written so that it has.
 */
class AnAnswerGuaranteesNothingWhereItHasNotRunYetTest {

    /**
     * {@code tagged} declares of every answer that it carries the number it was given, which its own
     * body cannot prove — {@code Nat} holds no negative number, and nothing rules a negative
     * argument out. So the declaration stands and the run-time check is what keeps it: a caller
     * that has come back from {@code tagged(x)} may take {@code x >= 0}, and one that has not
     * reached it may not.
     *
     * <p>{@code both} declares the same of an answer it is handed, so that the guarantee can be
     * asked about from inside one of its own arguments.
     */
    private static final String DECLARATIONS = """
            module demo exposing ( Nat, Pair, tagged, both, run )

            data Nat = Int
                invariant value >= 0

            data Pair = { l: Nat, r: Nat }

            behavior tagged : (n: Int) -> Nat
                constructs Nat
                ensures value.value == n
            let tagged (n) = Nat(n)

            behavior both : (a: Nat, n: Int) -> Nat
                ensures value.value == n
            let both (a, n) = a

            behavior run : (a: Nat, x: Int) -> Pair
                constructs Pair, Nat
            """;

    /** How many constructions the compile leaves owing a clause. */
    private static int unproven(String body) {
        List<Diagnostic> said = Compiler.compileWithWarnings(DECLARATIONS + body).warnings();
        return (int) said.stream()
                .filter(d -> d.severity() == Severity.WARNING)
                .filter(d -> d.code().equals("E2011"))
                .count();
    }

    /** {@code tagged}'s own body, which every source below carries and none of them can discharge. */
    private static final int THE_ONE_INSIDE_TAGGED = 1;

    /**
     * A field is judged under what the fields before it answered and not under what the fields after
     * it will.
     *
     * <p>{@code Pair} declares {@code l} and then {@code r}, and that is the order they run in — so
     * the same two expressions written the two ways round are one program evaluated in two orders,
     * and what the call guarantees reaches the construction in exactly one of them.
     */
    @Test
    void aLaterFieldGuaranteesNothingToAnEarlierOne() {
        assertEquals(THE_ONE_INSIDE_TAGGED,
                unproven("let run (a, x) = Pair { l = tagged(x), r = Nat(x) }\n"),
                "the call runs first, so `x >= 0` holds where the construction is judged");
        assertEquals(THE_ONE_INSIDE_TAGGED + 1,
                unproven("let run (a, x) = Pair { l = Nat(x), r = tagged(x) }\n"),
                "the call runs second, so nothing it guarantees is true where the construction is"
                        + " judged — and a reading that took it there would discharge a clause out"
                        + " of a value the program has not produced");
    }

    /**
     * An argument is judged under nothing the call it is written in guarantees.
     *
     * <p>A call answers after the values it was given have answered, so a guarantee about its answer
     * standing while one of its arguments is judged is a fact arriving before the evaluation that
     * makes it true. The construction is what decides whether that call is reached at all.
     */
    @Test
    void aCallGuaranteesNothingToItsOwnArgument() {
        assertEquals(THE_ONE_INSIDE_TAGGED,
                unproven("""
                        let run (a, x) = {
                            let g = both(a, x)
                            Pair { l = Nat(x), r = g }
                        }
                        """),
                "the call has answered where the construction stands, so what it guarantees holds");
        assertEquals(THE_ONE_INSIDE_TAGGED + 1,
                unproven("let run (a, x) = Pair { l = both(Nat(x), x), r = a }\n"),
                "the construction is one of the values that call is waiting on, so what the call"
                        + " guarantees is not something to judge it by");
    }
}
