package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A relation among the counts of one container's elements is something that container is asked,
 * and is asked of it as a count is, so a group of nothing else is the container's own: it is the
 * composer of the container that says whether the counts the relation weighs are asked beside it,
 * and says which are not. Not a group that has no way of being written at all, and not one that
 * has no number to be handed to.
 */
class ARelationAmongCountsAskedAloneIsAGroupOfItsContainerTest {

    private static final TermPath XS = TermPath.of("xs");

    @Test
    void aRelationAskedAloneIsComposedElementByElementForItsContainer() {
        NumericTerm element = new NumericTerm.ValueOf(XS.element());
        Proposition above = new Proposition.Compared(new Relation.Affine(new LinearForm<>(
                ExactRatio.ZERO,
                Map.of(new DecisionAtom.OfTheInput(element), ExactRatio.ONE)), Rel.GT), true);
        SequencedMap<Quantity.HowManyMeet, ExactRatio> counts = new LinkedHashMap<>();
        counts.put(new Quantity.HowManyMeet(new DecisionSubject.AnInput(XS), above),
                ExactRatio.ONE);
        AggregateRelation relation =
                new AggregateRelation(XS, counts, ExactRatio.ZERO, ExactRatio.of(-1), Rel.EQ);

        TermRealizations.JointRealization way = TermRealizations.jointRealizationOf(
                List.of(new RealizationTarget.CountsRelated(relation)));

        TermRealizations.JointBuilder.ElementByElement builder = assertInstanceOf(
                TermRealizations.JointBuilder.ElementByElement.class,
                assertInstanceOf(TermRealizations.JointRealization.Supported.class, way,
                        way.toString()).builder());
        assertEquals(XS, builder.container());
        assertEquals(List.of(relation), builder.related());
    }
}
