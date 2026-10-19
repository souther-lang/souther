package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison that is only reached where two values differ has no row where they are equal, and
 * the report says that rather than reaching for a figure.
 *
 * <p>The second comparison of {@code if sign == 0 ... else if sign < 0} is reached only where the
 * first was false, so {@code a != b}, and the point it asks for beside its edge is {@code a == b}.
 * The two cannot hold together, which is a finite proof; handed to a search instead, the pair is
 * tried at every place the figure allows and the report names the figure.
 */
class AComparisonReachedOnlyWhereTheValuesDifferHoldsNoRowAtItsEqualSideTest {

    private static final String REACHED_WHERE_THEY_DIFFER = """
            module p
            behavior settle : (a: Int, b: Int) -> Int
            let settle (a, b) = {
                let sign = Int.compare(a, b)
                if sign == 0 then 0 else if sign < 0 then 1 else 2
            }
            example settle
                | "eq" : (10, 10) -> 0
                | "lt" : (5, 10) -> 1
                | "gt" : (15, 10) -> 2
            """;

    /** The same comparison reached for every row, so a row where the two are equal can be written. */
    private static final String REACHED_WHEREVER = """
            module p
            behavior settle : (a: Int, b: Int) -> Int
            let settle (a, b) = {
                let sign = Int.compare(a, b)
                if sign < 0 then 1 else 2
            }
            example settle
                | "eq" : (10, 10) -> 2
                | "lt" : (5, 10) -> 1
                | "gt" : (15, 10) -> 2
            """;

    /** The else of {@code x == y} leaves {@code x != y}, and the comparison after it is worked out. */
    private static final String AFTER_THE_ELSE_OF_AN_EQUALITY = """
            module p
            data Eq
            data Lt
            data Gt
            behavior a : (x: Int, y: Int) -> Eq | Lt | Gt
            let a (x, y) = if x == y then Eq else if x < y then Lt else Gt
            """;

    private static String report(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    @Test
    void theEqualSideIsSaidToHoldNoRowAndNoFigureIsNamed() {
        String human = report(REACHED_WHERE_THEY_DIFFER);

        assertFalse(human.contains("how many places a pair is tried at"), human);
        assertTrue(human.contains("no row can stand at the OFF point (comparison@5:38)"), human);
    }

    @Test
    void aComparisonAfterTheElseOfAnEqualityOfTheSameTwoValuesIsWorkedOut() {
        String human = report(AFTER_THE_ELSE_OF_AN_EQUALITY);

        assertFalse(human.contains("not accounted for"), human);
    }

    /** Without it a proof of every OFF point of a comparison would pass the case above. */
    @Test
    void whereTheEqualSideIsReachedNoRowIsSaidToBeOutOfReach() {
        String human = report(REACHED_WHEREVER);

        assertFalse(human.contains("no row can stand at the"), human);
    }
}
