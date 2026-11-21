package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The ways an operation over several values a run works out is over numbers of the input are as
 * many as the product of the ways of each, and are given to a reader one at a time, as many as it
 * asks for: a reader that spends a figure on each it looks at is never handed the product before it
 * has spent any.
 */
class AnOperationOverSeveralValuesIsAttainedOnlyAsFarAsItIsAskedTest {

    private static final BigInteger EVERYTHING = BigInteger.valueOf(Long.MAX_VALUE);

    /** A value that comes to either of two numbers, as a row makes it. */
    private static UndividedByARelation.IntOperand valueOf(String name, long one, long other) {
        return new UndividedByARelation.IntOperand.OfAValueWorkedOut(
                new NumericTerm.ValueOf(TermPath.of(name)),
                new WhereAValueComesFrom.Fixed(new FormRange(ExactRatio.of(one),
                        ExactRatio.of(other))),
                List.of(Attainment.always(LinearForm.constant(ExactRatio.of(one))),
                        Attainment.always(LinearForm.constant(ExactRatio.of(other)))));
    }

    private static UndividedByARelation.IntOperation overTheSumOf(
            UndividedByARelation.IntOperand... operands) {
        List<LinearForm<UndividedByARelation.IntOperand>> atoms = new ArrayList<>();
        for (UndividedByARelation.IntOperand each : operands) {
            atoms.add(LinearForm.atom(each));
        }
        return new UndividedByARelation.IntOperation(LinearForm.sum(atoms).orNull(),
                EVERYTHING.negate(), EVERYTHING, List.of());
    }

    @Test
    void everyWayOfEverySeveralValuesIsVisitedWhereTheReaderAsksForAll() {
        UndividedByARelation.IntOperation sum = overTheSumOf(valueOf("a", 0, 1),
                valueOf("b", 0, 10), valueOf("c", 0, 100));
        Set<ExactRatio> comes = new TreeSet<>();
        sum.forEachAttained(way -> comes.add(way.form().constant()));
        assertEquals(8, comes.size(), "two ways of each of three values, which no two of "
                + "put to one number");
    }

    @Test
    void noMoreWaysAreVisitedThanTheReaderAsksFor() {
        UndividedByARelation.IntOperation sum = overTheSumOf(valueOf("a", 0, 1),
                valueOf("b", 0, 10), valueOf("c", 0, 100));
        int[] visited = {0};
        sum.forEachAttained(_ -> ++visited[0] < 3);
        assertEquals(3, visited[0], "the third is the last asked for");
    }

    @Test
    void nothingIsVisitedWhereSomeValueHasNoWay() {
        UndividedByARelation.IntOperand none = new UndividedByARelation.IntOperand
                .OfAValueWorkedOut(new NumericTerm.ValueOf(TermPath.of("n")),
                new WhereAValueComesFrom.Fixed(new FormRange(ExactRatio.ZERO, ExactRatio.ONE)),
                List.of());
        UndividedByARelation.IntOperation sum = overTheSumOf(valueOf("a", 0, 1), none);
        int[] visited = {0};
        sum.forEachAttained(_ -> ++visited[0] > 0);
        assertEquals(0, visited[0]);
    }
}
