package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Relation;
import souther.compiler.meaning.Spelling;
import souther.compiler.meaning.WrittenLine;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A case that is one relation is said as that relation, in the scale and direction every writing of
 * it comes to; a case of several parts is not said, since two spellings of one line take the
 * statement apart differently.
 */
class ACaseSaidAsARelationIsSaidInOneScaleWhicheverWayItWasWrittenTest {

    private static Proposition compared(String at, long weight, Rel rel, long than,
                                        boolean holds) {
        return new Proposition.Compared(new Relation.Affine(new LinearForm<>(
                ExactRatio.of(-than), Map.of(new DecisionAtom.OfTheInput(
                        new NumericTerm.ValueOf(TermPath.of(at))), ExactRatio.of(weight))), rel),
                holds);
    }

    private static Optional<String> said(Proposition decides) {
        return new WhereAPartDecides(new PlaceOfALine(PartOfAComparison.of(
                WrittenLine.THE_COMPARISON), Spelling.of("line")), decides).asOneRelation();
    }

    @Test
    void aRelationAndItsDenialAreSaidAsTheyAre() {
        assertEquals(Optional.of("n > 50"), said(compared("n", 1, Rel.GT, 50, true)));
        assertEquals(Optional.of("n <= 50"), said(compared("n", 1, Rel.GT, 50, false)));
        assertEquals(Optional.of("n /= 50"), said(compared("n", 1, Rel.EQ, 50, false)));
        assertEquals(Optional.of("n == 50"), said(compared("n", 1, Rel.EQ, 50, true)));
    }

    @Test
    void aRelationScaledIsSaidAsItIsNot() {
        assertEquals(said(compared("k", 1, Rel.GE, 2, false)),
                said(compared("k", 2, Rel.GE, 4, false)));
        assertEquals(Optional.of("k < 2"), said(compared("k", 2, Rel.GE, 4, false)));
    }

    @Test
    void aCaseOfSeveralPartsIsNotSaid() {
        assertEquals(Optional.empty(), said(Proposition.all(List.of(
                compared("n", 1, Rel.GT, 50, true), compared("m", 1, Rel.GT, 0, true)))));
        assertEquals(Optional.empty(), said(Proposition.any(List.of(
                compared("n", 1, Rel.GT, 50, true), compared("m", 1, Rel.GT, 0, true)))));
    }
}
