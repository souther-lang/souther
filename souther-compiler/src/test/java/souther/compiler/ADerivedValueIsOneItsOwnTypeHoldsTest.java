package souther.compiler;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a recipe works out to can be a number the value it is about never is, and the value's own
 * kind of number is what says so.
 *
 * <p>The arithmetic a form is read through composes numbers of any size. What an operation answers
 * is a value of its own type, and where the two disagree it is the arithmetic that ran wide: the
 * quotient of the smallest {@code Int} by minus one works out to one past the whole-number range,
 * and the operation that would have answered it aborts instead (spec §stdlib-int). Held anyway, a
 * reading <em>refused</em> a construction over a value no program ever builds — an error, on a path
 * nothing reaches.
 *
 * <p>What it comes to is that the divide answers nothing here, so nothing carries on from it and the
 * arms below it are entered by no run. Neither construction is judged, and which of them the author
 * wrote does not decide it — the arm reached over the quotient and the arm reached over anything
 * else are one arm, and a check that refused the first and owed the second was answering a question
 * about reachability with a reading of the values (#980).
 *
 * <p>Read of the carrier and not of a declaration. A value of a newtype has satisfied that
 * newtype's invariant, and whether a construction does is the question being asked — so the range
 * read here is the machine's, which is true of every value that exists at all.
 */
class ADerivedValueIsOneItsOwnTypeHoldsTest {

    private static List<String> reported(String model) {
        return Compiler.compileWithWarnings(model).warnings().stream()
                .map(Diagnostic::code)
                .distinct()
                .toList();
    }

    /**
     * The one pair whose quotient no {@code Int} holds. Nothing comes back from the divide, so
     * neither arm is entered and there is nothing under them to report — where a reading that worked
     * the quotient out to a positive number refused the construction for being positive.
     */
    @Test
    void aQuotientNoIntHoldsLeavesTheArmWithNoValue() {
        assertEquals(List.of(), reported("""
                module demo

                data Negative = Int
                    invariant value < 0

                data Nothing

                behavior 割る : (a: Int) -> Negative | Nothing
                    constructs Negative
                let 割る (a) = {
                    guard a == (0 - 9223372036854775807) - 1 else Nothing
                    match Int.divide(a, 0 - 1) with
                        | Int as q -> Negative(q)
                        | DivisionByZero -> Nothing
                }
                """));
    }

    /**
     * The same where the arithmetic runs off one end only.
     *
     * <p>An {@code Int} at or below the smallest one is that one, so the divide answers nothing here
     * as surely as it does above — and what the quotient works out to is every number past the
     * largest {@code Int}, which is a range with an end at one side and none at the other. Nothing
     * of it is a value, and a correction that only pulled the end it has back would leave the range
     * holding numbers no {@code Int} is, and refusing the construction by one of them.
     */
    @Test
    void aQuotientRunningOffOneEndOnlyLeavesNoValueEither() {
        assertEquals(List.of(), reported("""
                module demo

                data Negative = Int
                    invariant value < 0

                data Nothing

                behavior 割る : (a: Int) -> Negative | Nothing
                    constructs Negative
                let 割る (a) = {
                    guard a <= (0 - 9223372036854775807) - 1 else Nothing
                    match Int.divide(a, 0 - 1) with
                        | Int as q -> Negative(q)
                        | DivisionByZero -> Nothing
                }
                """));
    }

    /**
     * The control, and silence is not what the two above are read off. The very same construction
     * over a dividend one greater has a quotient an {@code Int} holds, so the divide answers, the
     * arm is entered, and the value is judged: it is positive where the invariant wants a negative,
     * which is an error. What the rows above must not reach is that refutation, and this is the
     * evidence they could have — the rule runs, and it is what the divide answers that stops it.
     */
    @Test
    void aQuotientThatDoesFitIsJudgedOnItsValue() {
        CompileException refused = assertThrows(CompileException.class, () -> reported("""
                module demo

                data Negative = Int
                    invariant value < 0

                data Nothing

                behavior 割る : (a: Int) -> Negative | Nothing
                    constructs Negative
                let 割る (a) = {
                    guard a == 0 - 9223372036854775807 else Nothing
                    match Int.divide(a, 0 - 1) with
                        | Int as q -> Negative(q)
                        | DivisionByZero -> Nothing
                }
                """));
        assertTrue(refused.getMessage().contains("E2010"), refused.getMessage());
    }
}
