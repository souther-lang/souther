package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The ways an operation over several values a run works out is over numbers of the input are as
 * many as the product of the ways of each, and are given to a reader one at a time, as many as it
 * asks for: a reader that spends a figure on each it looks at is never handed the product before it
 * has spent any. Each way keeps what every value's way asks of a row, so ways that ask different
 * things of one number are not a way for any row; and where a value's ways were left unmade for
 * want of the figure, that is said and is not a value that has none.
 */
class AnOperationOverSeveralValuesIsAttainedOnlyAsFarAsItIsAskedTest {

    private static final BigInteger EVERYTHING = BigInteger.valueOf(Long.MAX_VALUE);

    private static final NumericTerm HOW_MANY = new NumericTerm.ValueOf(TermPath.of("n"));

    /** A value that comes to either of two numbers, as a row makes it. */
    private static UndividedByARelation.IntOperand valueOf(String name, long one, long other) {
        return valueOf(name, Attainments.of(List.of(
                Attainment.always(LinearForm.constant(ExactRatio.of(one))),
                Attainment.always(LinearForm.constant(ExactRatio.of(other))))));
    }

    private static UndividedByARelation.IntOperand valueOf(String name, Attainments ways) {
        return new UndividedByARelation.IntOperand.OfAValueWorkedOut(
                new NumericTerm.ValueOf(TermPath.of(name)),
                new WhereAValueComesFrom.Fixed(new FormRange(ExactRatio.ZERO, ExactRatio.ONE)),
                ways);
    }

    /** A value of the one number {@code to}, for the rows where the list counted holds
     *  {@code size}. */
    private static UndividedByARelation.IntOperand valueWhere(String name, long to, long size) {
        return valueOf(name, Attainments.of(List.of(new Attainment(
                LinearForm.constant(ExactRatio.of(to)),
                List.of(new TakenConstraint.Affine(LinearForm.atomMinusConstant(HOW_MANY,
                        ExactRatio.of(size)), Rel.EQ))))));
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
        assertTrue(sum.forEachAttained(way -> comes.add(way.form().constant())));
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
        UndividedByARelation.IntOperation sum = overTheSumOf(valueOf("a", 0, 1),
                valueOf("n", Attainments.NONE));
        int[] visited = {0};
        assertTrue(sum.forEachAttained(_ -> ++visited[0] > 0),
                "a value no rule says a way for is no value left unmade");
        assertEquals(0, visited[0]);
    }

    @Test
    void whereSomeValuesWaysWereLeftUnmadeThatIsSaidAndWhatWasMadeIsVisited() {
        UndividedByARelation.IntOperation sum = overTheSumOf(valueOf("a", 0, 1),
                valueOf("n", Attainments.TOO_MANY));
        int[] visited = {0};
        assertFalse(sum.forEachAttained(_ -> ++visited[0] > 0));
        assertEquals(0, visited[0], "a value of no ways made leaves the sum no way to visit");
    }

    /** One value asks the list counted to hold none and another asks it to hold one, so no number
     *  of it meets both: a way that put them together without keeping both is one a row meets. */
    @Test
    void waysThatAskDifferentThingsOfOneNumberAreNotAWayForAnyRow() {
        UndividedByARelation.IntOperation sum = overTheSumOf(valueWhere("a", 5, 0),
                valueWhere("b", 7, 1));
        int[] visited = {0};
        sum.forEachAttained(way -> {
            visited[0]++;
            assertEquals(2, way.holding().size(), "what each value asks is kept");
            for (long size = 0; size <= 2; size++) {
                Map<NumericTerm, ExactRatio> at = Map.of(HOW_MANY, ExactRatio.of(size));
                assertFalse(way.holding().stream()
                        .allMatch(each -> WholeValuesMeeting.holdsAt(each, at)),
                        "no list holds both counts: " + size);
            }
            return true;
        });
        assertEquals(1, visited[0]);
    }
}
