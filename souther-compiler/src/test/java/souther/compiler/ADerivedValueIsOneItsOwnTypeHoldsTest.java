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
 * and the operation that would have answered it aborts instead (spec §stdlib-int). So the value
 * exists on no run, and a reading holding it could refuse a construction over a value no program
 * ever builds.
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
     * The one pair whose quotient no {@code Int} holds. The arm is reached on no run — the divide
     * aborts — so the construction under it is owed nothing, and a reading that worked the quotient
     * out to a positive number would refuse it for being positive.
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
     * The control: the very same construction over a dividend one greater, whose quotient is a
     * number an {@code Int} holds and is positive. A negative it is not, so the values refuse the
     * construction, which is an error and not a warning — and it is the very refutation the row
     * above must not reach, over a value that does exist.
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
