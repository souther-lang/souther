package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.Refinement;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What an element adds to a total through a place is what its case makes of it, and cases may make
 * the same place a different amount: a movement in adds the quantity and one out takes it off. A
 * total of so much is reached by an element of each of those at a different figure, so the figure
 * of each case, and of what no case names, is a place to stand at
 * ({@link CardinalityComposer#addedThrough}).
 */
class EveryFormAnElementsCaseAddsThroughAPlaceIsOneTheTotalIsReachedByTest {

    private static final ElementProjection QTY = ElementProjection.ofFields(List.of("qty"));

    private static final ElementProjection DIRECTION = ElementProjection.ofFields(List.of("dir"));

    private static ElementValue.Affine weighed(long by) {
        return new ElementValue.Affine(new LinearForm<>(ExactRatio.ZERO,
                Map.of(QTY, ExactRatio.of(by))));
    }

    private static ElementValue.OfItsCase.Arm taking(String leaf, ElementValue value) {
        return new ElementValue.OfItsCase.Arm(CasesLeft.ofEach(List.of(Refinement.of(
                new Case.SumCase(TypeSymbols.declared(new TypeKey("probe", leaf)), true)))),
                value);
    }

    @Test
    void theFormOfEveryCaseTheTotalIsAddedThroughIsOffered() {
        ElementValue in = weighed(1);
        ElementValue out = weighed(-1);
        ElementValue chosen = new ElementValue.OfItsCase(DIRECTION,
                List.of(taking("In", in), taking("Out", out)), null);
        assertEquals(List.of(in, out), CardinalityComposer.addedThrough(chosen, QTY));
    }

    @Test
    void whatNoCaseNamesIsOfferedBesideTheCases() {
        ElementValue in = weighed(1);
        ElementValue out = weighed(-1);
        ElementValue chosen = new ElementValue.OfItsCase(DIRECTION, List.of(taking("In", in)), out);
        assertEquals(List.of(in, out), CardinalityComposer.addedThrough(chosen, QTY));
    }

    @Test
    void aFormTwoCasesShareIsOfferedOnce() {
        ElementValue in = weighed(1);
        ElementValue chosen = new ElementValue.OfItsCase(DIRECTION,
                List.of(taking("In", in), taking("Out", in)), weighed(2));
        assertEquals(List.of(in, weighed(2)), CardinalityComposer.addedThrough(chosen, QTY));
    }

    @Test
    void aCaseAddingNothingThroughThePlaceOffersNothing() {
        ElementValue elsewhere = new ElementValue.Affine(new LinearForm<>(ExactRatio.ZERO,
                Map.of(ElementProjection.ofFields(List.of("other")), ExactRatio.ONE)));
        ElementValue chosen = new ElementValue.OfItsCase(DIRECTION,
                List.of(taking("In", weighed(1)), taking("Out", elsewhere)), null);
        assertEquals(List.of(weighed(1)), CardinalityComposer.addedThrough(chosen, QTY));
    }
}
