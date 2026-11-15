package souther.compiler;

import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Severity;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * What a walk's step adds at most bounds the list the walk grows, and only that walk's list: two
 * walks in one model whose steps add one and two elements are bounded by one and by two, and the
 * bound of the shorter is not carried to the longer however the two are reached.
 */
class AListAWalkGrowsHoldsNoMoreThanItsOwnStepAddsTest {

    private static final String DECLARES = """
            module m exposing ( AtMostTwo, once, twice )

            data AtMostTwo = Int
                invariant value <= 2

            behavior once : (xs: List<Int>) -> AtMostTwo
                constructs AtMostTwo

            behavior twice : (xs: List<Int>) -> AtMostTwo
                constructs AtMostTwo
            """;

    private static List<Diagnostic> unproven(String source) {
        return Compiler.compileWithWarnings(source).warnings().stream()
                .filter(d -> d.severity() == Severity.WARNING)
                .filter(d -> d.code().equals("E2011")).toList();
    }

    private static String bodies(String onceStep, String twiceStep) {
        return DECLARES + """
                let once (xs) = {
                    guard List.length(xs) <= 2
                        else AtMostTwo(0)
                    AtMostTwo(List.length(List.flatMap(x -> %s, xs)))
                }

                let twice (xs) = {
                    guard List.length(xs) <= 2
                        else AtMostTwo(0)
                    AtMostTwo(List.length(List.flatMap(x -> %s, xs)))
                }
                """.formatted(onceStep, twiceStep);
    }

    /** The control: a step adding one element over at most two elements holds at most two. */
    @Test
    void aStepAddingOneElementBoundsTheListByTheElementsWalked() {
        assertEquals(List.of(), unproven(bodies("[x]", "[x]")),
                "one element at most for each of at most two is two at most");
    }

    /** A step adding two elements over at most two holds as many as four, which the bound of two
     *  does not cover, whichever of the two behaviors is read first. */
    @Test
    void aStepAddingTwoElementsIsNotBoundedByWhatAStepAddingOneIs() {
        assertFalse(unproven(bodies("[x]", "[x, x]")).isEmpty(),
                "the second behavior's list can hold four");
        assertFalse(unproven(bodies("[x, x]", "[x]")).isEmpty(),
                "and so can the first's, read after or before the other");
    }
}
