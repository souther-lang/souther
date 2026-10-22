package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.check.NewtypeInners;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.ElementProjection;
import souther.compiler.inputs.ElementValue;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.RunSource;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Totals of one container's elements are a group one builder composes where each of them adds up
 * a field of its own, or a form of one field, and no other total reads that field. Any other
 * group is one no builder solves, and is said to be one rather than composed in part.
 */
class AGroupOfTotalsIsComposedTogetherOnlyWhereEachReadsAFieldOfItsOwnTest {

    private static final TermPath ELEMENTS = TermPath.of("r").then("lines").element();

    private static ElementProjection field(String name) {
        return ElementProjection.ofFields(List.of(name));
    }

    /** {@code const + Σ coef·field}, the computation a lambda over an element makes. */
    private static ElementValue form(int constant, Map<String, Integer> weights) {
        Map<ElementProjection, ExactRatio> coefs = new LinkedHashMap<>();
        weights.forEach((name, weight) -> coefs.put(field(name), ExactRatio.of(weight)));
        return new ElementValue.Affine(new LinearForm<>(ExactRatio.of(constant), coefs));
    }

    private static RealizationTarget total(ElementValue computation) {
        NumericTerm.TakenOver over = NumericTerm.TakenOver.of(
                ValueName.Stdlib.operation("List", "sum"),
                new RunSource.ComputedOccurrences(ELEMENTS, computation, Type.Prim.INT, null),
                Type.Prim.INT, NewtypeInners.NONE, Symbols.none(DefaultStdlib.get()));
        assertNotNull(over, "a total over what is computed of each element is a number of a run");
        return RealizationTarget.of(over);
    }

    private static RealizationTarget totalOf(String name) {
        return total(form(0, Map.of(name, 1)));
    }

    private static TermRealizations.JointBuilder.TotalsOfOneContainer composed(
            RealizationTarget... group) {
        TermRealizations.JointRealization way =
                TermRealizations.jointRealizationOf(List.of(group));
        return assertInstanceOf(TermRealizations.JointBuilder.TotalsOfOneContainer.class,
                assertInstanceOf(TermRealizations.JointRealization.Supported.class, way,
                        () -> "a group the totals are composed together for: " + way).builder());
    }

    private static void noBuilder(RealizationTarget... group) {
        TermRealizations.JointRealization way =
                TermRealizations.jointRealizationOf(List.of(group));
        TermRealizations.JointRealization.Missing missing = assertInstanceOf(
                TermRealizations.JointRealization.Missing.class, way,
                () -> "a group no builder solves is said so, and not composed in part: " + way);
        assertEquals(CompositionRepertoire.VALUES_THAT_ANSWER_SEVERAL_OF_THEIR_NUMBERS,
                missing.notAllOf(), "and says which population it wrote none of");
    }

    @Test
    void totalsOfFieldsOfTheirOwnAreOneBuilder() {
        assertEquals(2, composed(totalOf("a"), totalOf("b")).whatItComesTo().size());
    }

    @Test
    void thereIsNoLimitOfTwoTotals() {
        assertEquals(3, composed(totalOf("a"), totalOf("b"), totalOf("c")).whatItComesTo().size());
    }

    @Test
    void aFormOfAFieldBesideAFieldOfItsOwnIsOneBuilder() {
        assertEquals(2, composed(total(form(3, Map.of("a", 2))), totalOf("b"))
                .whatItComesTo().size());
    }

    @Test
    void aTotalOfThePathBesideAComputedOneIsOneBuilder() {
        NumericTerm.TakenOver projected = NumericTerm.TakenOver.of(
                ValueName.Stdlib.operation("List", "sum"),
                RunSource.overTheOccurrencesAt(ELEMENTS.then("a")), Type.Prim.INT,
                NewtypeInners.NONE, Symbols.none(DefaultStdlib.get()));
        assertNotNull(projected);
        assertEquals(2, composed(RealizationTarget.of(projected), totalOf("b"))
                .whatItComesTo().size());
    }

    @Test
    void twoTotalsOfOneFieldAreNoBuilder() {
        noBuilder(totalOf("a"), total(form(0, Map.of("a", 2))));
    }

    @Test
    void aTotalOfTwoFieldsBesideATotalOfOneOfThemIsNoBuilder() {
        noBuilder(totalOf("a"), total(form(0, Map.of("a", 1, "b", 1))));
    }

    @Test
    void aTotalOfTwoFieldsBesideTotalsOfFieldsOfTheirOwnIsNoBuilder() {
        noBuilder(totalOf("a"), totalOf("b"), total(form(0, Map.of("c", 1, "d", 1))));
    }
}
