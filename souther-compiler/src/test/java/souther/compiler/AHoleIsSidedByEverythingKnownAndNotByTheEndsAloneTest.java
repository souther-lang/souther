package souther.compiler;

import java.util.List;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Diagnostic;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A {@code /=} states no half-space of its own, and which side of the value the sum falls is read
 * off everything known rather than off each position's own range.
 *
 * <p>A sum is held by things no position's range carries — a relation between two of them, a rule
 * naming a third. Sided by the ranges alone, a {@code guard} writing {@code /=} beside a relation
 * stated nothing, while the same {@code /=} beside a range on the value itself was read. Which of
 * those an author wrote is not a distinction the language makes.
 *
 * <p>What makes each row here derivable is the whole numbers: a sum above nought and away from it
 * is at one, so the hole is what turns a bound that does not discharge {@code value >= 1} into one
 * that does.
 */
class AHoleIsSidedByEverythingKnownAndNotByTheEndsAloneTest {

    private static List<String> reported(String guard) {
        return Compiler.compileWithWarnings("""
                module demo

                data Positive = Int
                    invariant value >= 1

                behavior f : (a: Int, b: Int) -> Positive
                    constructs Positive

                let f (a, b) = {
                    guard %s else Positive(1)
                    Positive(a)
                }
                """.formatted(guard)).warnings().stream().map(Diagnostic::code).toList();
    }

    /** What the ranges answer on their own, which they did before this and still do. */
    @Test
    void aHoleAtTheEndOfAPositionsOwnRangeSidesIt() {
        assertEquals(List.of(), reported("a >= 0 && a /= 0"));
    }

    /** The same argument through a difference, which is held by the closed relations and by neither
     *  position's range. */
    @Test
    void aHoleOverADifferenceIsSidedByTheRelationThatHoldsIt() {
        assertEquals(List.of(), reported("b >= 0 && b <= 5 && a - b >= 0 && a - b /= 0"));
    }

    /**
     * And through a sum the relations cannot hold.
     *
     * <p>Weighed ten and minus one, so it is a rule rather than a difference and the closure holds
     * nothing about it as a pair. It sides the hole all the same, which is the half of this that
     * reading the relations alone does not answer.
     */
    @Test
    void aHoleOverASumTheRelationsCannotHoldIsSidedByTheRuleThatDoes() {
        assertEquals(List.of(),
                reported("b >= 0 && b <= 5 && a * 10 - b >= 0 && a * 10 - b /= 0"));
    }

    /**
     * The control, and the reason the rows above mean anything.
     *
     * <p>The same guards with the hole taken out. Nothing then puts {@code a} above nought, so the
     * construction is owed and the report is the check working.
     */
    @Test
    void withoutTheHoleThereIsNothingToSideAndItIsStillReported() {
        assertEquals(List.of("E2011"), reported("b >= 0 && b <= 5 && a - b >= 0"));
    }
}
