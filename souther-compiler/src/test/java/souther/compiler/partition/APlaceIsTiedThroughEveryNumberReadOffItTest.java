package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The places a way ties are those every number of a statement is read off: a product of the
 * numbers of two places ties them, though neither factor is a number of one place standing alone
 * in the statement.
 */
class APlaceIsTiedThroughEveryNumberReadOffItTest {

    private static final TermPath A = TermPath.of("a");
    private static final TermPath B = TermPath.of("b");
    private static final TermPath C = TermPath.of("c");

    private static TakenConstraint.Affine isOne(NumericTerm term) {
        return new TakenConstraint.Affine(
                new LinearForm<>(ExactRatio.of(-1), Map.of(term, ExactRatio.ONE)), Rel.EQ);
    }

    /** The statement says no positions of its own, so what it ties is read off its numbers
     *  alone. */
    @Test
    void aProductOfTwoPlacesNumbersTiesThem() {
        NumericTerm product = NumericTerm.ProductOf.of(
                LinearForm.atom(new NumericTerm.ValueOf(A)),
                LinearForm.atom(new NumericTerm.ValueOf(B)));
        UndividedByARelation.OnAWay statement =
                new UndividedByARelation.OnAWay(Set.of(), false, isOne(product), null);
        PlacesTiedAlongAWay way = PlacesTiedAlongAWay.of(List.of(statement), List.of(),
                List.of(A, B, C), _ -> null, _ -> false);

        assertEquals(Set.of(A, B), way.tiedTo(A));
        assertEquals(Set.of(C), way.tiedTo(C));
    }
}
