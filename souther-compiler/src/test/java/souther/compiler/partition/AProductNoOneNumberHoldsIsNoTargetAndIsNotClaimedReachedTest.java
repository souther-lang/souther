package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A product of two forms no one number holds at a value is a number no row writes, so it has no
 * target, and a search over it says it was not shown to be reached rather than stopping the run.
 */
class AProductNoOneNumberHoldsIsNoTargetAndIsNotClaimedReachedTest {

    private static NumericTerm number(String name) {
        return new NumericTerm.ValueOf(TermPath.of(name));
    }

    private static LinearForm<NumericTerm> sumOf(String first, String second) {
        return new LinearForm<>(ExactRatio.ZERO,
                Map.of(number(first), ExactRatio.ONE, number(second), ExactRatio.ONE));
    }

    /** {@code (a + b) * rate}: neither factor is a number alone beside a form of one number. */
    @Test
    void aSumTimesANumberHasNoWayAndNoTarget() {
        NumericTerm.ProductOf product = NumericTerm.ProductOf.of(sumOf("a", "b"),
                LinearForm.atom(number("rate")));
        assertNull(product.atAValue());
        assertEquals(Optional.empty(), RealizationTarget.of(product));
    }

    /** {@code (a + b) * (rate + r2)}. */
    @Test
    void aSumTimesASumHasNoWayAndNoTarget() {
        NumericTerm.ProductOf product = NumericTerm.ProductOf.of(sumOf("a", "b"),
                sumOf("rate", "r2"));
        assertNull(product.atAValue());
        assertEquals(Optional.empty(), RealizationTarget.of(product));
    }

    /** A product that has a way keeps the root of the number that carries it. */
    @Test
    void aProductWithAWayKeepsTheRootOfItsCarrier() {
        NumericTerm.ProductOf product = NumericTerm.ProductOf.of(LinearForm.atom(number("a")),
                LinearForm.atom(number("rate")));
        NumericTerm.ProductOf.AtAValue way = product.atAValue();
        assertNotNull(way);
        RealizationTarget.OfANumber target = RealizationTarget.of(product).orElseThrow();
        assertEquals(RealizationTarget.ofAPlace((NumericTerm.FromOnePosition) way.carrier())
                .writeRoot(), target.writeRoot());
    }

    /** A target of a product cannot be made without the number that carries it. */
    @Test
    void aProductTargetIsNotMadeBesideAnotherCarrierOrNone() {
        NumericTerm.ProductOf withAWay = NumericTerm.ProductOf.of(
                LinearForm.atom(number("a")), LinearForm.atom(number("rate")));
        NumericTerm.ProductOf withNone = NumericTerm.ProductOf.of(sumOf("a", "b"),
                LinearForm.atom(number("rate")));
        RealizationTarget.OfANumber other = RealizationTarget.ofAPlace(
                (NumericTerm.FromOnePosition) number("elsewhere"));
        assertThrows(IllegalArgumentException.class,
                () -> new RealizationTarget.OfAProduct(withAWay, other));
        assertThrows(IllegalArgumentException.class,
                () -> new RealizationTarget.OfAProduct(withNone, other));
    }

    /** Every target the factory makes answers its root, whatever kind of term it was made for. */
    @Test
    void everyTargetTheFactoryMakesHasARoot() {
        List<NumericTerm> terms = List.of(number("a"),
                NumericTerm.ProductOf.of(LinearForm.atom(number("a")),
                        LinearForm.atom(number("rate"))),
                NumericTerm.ProductOf.of(sumOf("a", "b"), LinearForm.atom(number("rate"))));
        for (NumericTerm term : terms) {
            RealizationTarget.of(term).ifPresent(target ->
                    assertNotNull(assertDoesNotThrow(target::writeRoot), term.toString()));
        }
    }

    private static String modelOf(String parameters, String net) {
        return """
                module t.m4 exposing ( Out, plan )

                data Out = { within: Bool }

                behavior plan : (%s) -> Out

                let plan (%s) = {
                    let net = %s
                    Out { within = Decimal.compare(net, limit) <= 0 }
                }
                """.formatted(parameters, parameters.replaceAll(":\\s*[A-Za-z]+", ""), net);
    }

    /**
     * The model measures, and no row is said to stand where no value can: a relation over a
     * product no row is written for is one not shown to be reached.
     */
    private static void assertMeasured(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        assertDoesNotThrow(() -> {
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
        }, model);
        assertNotNull(Adequacy.readingsOf(compilation.db(), "t.m4"), model);
        assertTrue(compilation.db().ask(new Adequacy.Coverage("t.m4")).value()
                .containsKey("plan"), model);
    }

    /** The reproduction, its two-sum form and its whole-number form measure. */
    @Test
    void aRelationOverAProductNoOneNumberHoldsIsMeasuredWithoutAnInternalError() {
        assertMeasured(modelOf("a: Decimal, b: Decimal, limit: Decimal, rate: Decimal",
                "Decimal.multiply(Decimal.add(a, b), rate)"));
        assertMeasured(modelOf(
                "a: Decimal, b: Decimal, limit: Decimal, rate: Decimal, r2: Decimal",
                "Decimal.multiply(Decimal.add(a, b), Decimal.add(rate, r2))"));
        assertMeasured(modelOf("a: Int, b: Int, c: Int, limit: Decimal",
                "Decimal.fromInt((a + b) * c)"));
    }

    /** The controls: a product that has a way, a sum beside a constant, and no product. */
    @Test
    void theControlsStillMeasure() {
        assertMeasured(modelOf("a: Decimal, b: Decimal, limit: Decimal, rate: Decimal",
                "Decimal.multiply(a, rate)"));
        assertMeasured(modelOf("a: Decimal, b: Decimal, limit: Decimal, rate: Decimal",
                "Decimal.multiply(Decimal.add(a, b), 0.1m)"));
        assertMeasured(modelOf("a: Decimal, b: Decimal, limit: Decimal, rate: Decimal",
                "Decimal.subtract(a, 1.0m)"));
    }
}
