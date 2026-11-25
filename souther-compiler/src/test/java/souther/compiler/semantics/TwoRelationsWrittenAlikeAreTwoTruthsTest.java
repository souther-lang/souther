package souther.compiler.semantics;

import org.junit.jupiter.api.Test;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether cases cover every way their arguments stand is read over the relations they are
 * reached under, each the relation it is and not the way it is written: two relations over two
 * arguments written alike are two truths, each of which may come out either way.
 */
class TwoRelationsWrittenAlikeAreTwoTruthsTest {

    /** An argument written as {@code x}, whichever it is. */
    private record Written(String name) {

        @Override
        public String toString() {
            return name.startsWith("x") ? "x" : name;
        }
    }

    private static final Written X1 = new Written("x1");
    private static final Written X2 = new Written("x2");
    private static final Written Y = new Written("y");

    private static DefinitionCase<Written> reachedWhere(Written left, Rel rel, Written right) {
        return new DefinitionCase<>(LinearForm.atom(left), List.of(
                new ArgumentsStand<>(LinearForm.atom(left), rel, LinearForm.atom(right))));
    }

    @Test
    void twoRelationsOverArgumentsWrittenAlikeAreTwo() {
        assertFalse(DefinitionCase.coverEveryWay(List.of(reachedWhere(X1, Rel.LT, Y),
                        reachedWhere(X2, Rel.GE, Y))),
                "x1 at y and x2 below it is reached by neither case");
    }

    @Test
    void oneRelationAndItsDenialCoverEveryWay() {
        assertTrue(DefinitionCase.coverEveryWay(List.of(reachedWhere(X1, Rel.LT, Y),
                reachedWhere(Y, Rel.LE, X1))), "x1 below y, or y at or below x1");
    }
}
