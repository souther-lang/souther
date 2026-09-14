package souther.compiler.check;

import souther.compiler.Compiler;
import souther.compiler.diag.CompileException;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A report about what a call applies quotes the name its author wrote, whatever a pass has since
 * put in the callee position.
 *
 * <p>{@code List.fold} is sugar for {@code List.foldFrom} from index zero, and the rewrite runs
 * before anything types the call. So every report about the call is written after the name the
 * author wrote has been replaced — and the operation it was replaced with is one the library keeps
 * to itself and takes another argument. A report quoting that sends its reader to look up a name
 * they may not write, in a call of a length they did not make.
 *
 * <p>Three reports, because the rewrite is one and the readers are not. They go through one
 * accessor today, and what they have in common is the question rather than the accessor: each is
 * about what this call applies, and the answer to that was settled when the call was read.
 *
 * <p>The negative is what carries the test. {@code List.foldFrom} contains {@code List.fold}, so a
 * report that quotes the operation passes a test that only looks for the sugar.
 */
class AReportQuotesTheNameTheAuthorAppliedTest {

    /** What the author wrote at every call below. */
    private static final String WROTE = "List.fold";

    /** What the rewrite puts there: a private operation of the library, taking one argument more. */
    private static final String STANDS_FOR = "List.foldFrom";

    @Test
    void whereTheStepAnswersSomethingTheAccumulatorCannotHold() {
        quotesWhatWasWritten("""
                module m

                behavior tally : (xs: List<Int>) -> Int
                let tally (xs) = List.fold((acc, x) -> "no", 0, xs)
                """);
    }

    @Test
    void whereAnArgumentIsNotWhatItsPositionTakes() {
        quotesWhatWasWritten("""
                module m

                behavior tally : (xs: List<Int>) -> Int
                let tally (xs) = List.fold((acc, x) -> acc + x, "seed", xs)
                """);
    }

    @Test
    void whereTheBlockItTakesIsNotWritten() {
        quotesWhatWasWritten("""
                module m

                behavior tally : (xs: List<Int>) -> Int
                let tally (xs) = List.fold(1, 0, xs)
                """);
    }

    /**
     * And the numbering is the author's too. The rewrite supplies its argument after the ones that
     * were written, so an argument the author can count to is the one the report names.
     */
    @Test
    void andAnArgumentIsNumberedAmongTheOnesThatWereWritten() {
        CompileException refused = quotesWhatWasWritten("""
                module m

                behavior tally : (n: Int) -> Int
                let tally (n) = List.fold((acc, x) -> acc + x, 0, n)
                """);

        assertTrue(refused.getMessage().contains("argument 3 of " + WROTE),
                () -> "the list is the third of the three the author wrote: " + refused.getMessage());
    }

    private static CompileException quotesWhatWasWritten(String source) {
        CompileException refused = refusing(source);

        assertFalse(refused.getMessage().contains(STANDS_FOR),
                () -> "`" + STANDS_FOR + "` is not a name this author wrote, nor one they may: "
                        + refused.getMessage());
        assertTrue(refused.getMessage().contains(WROTE),
                () -> "and `" + WROTE + "` is what they did write: " + refused.getMessage());
        return refused;
    }

    private static CompileException refusing(String source) {
        return assertThrows(CompileException.class, () -> Compiler.compile(source));
    }
}
