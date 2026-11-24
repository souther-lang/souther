package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a domain says about one position is what the part of the rules weighing that position says,
 * and the parts are put together only for a question that spans them.
 *
 * <p>Held as a shape. The answers are the same whether the parts are put together first or not, and
 * the theorem tests of the product see a wrong one; what nothing that compares answers can see is a
 * question about one position that puts every part together to find them, which is a cost in every
 * question asked of a domain with many parts.
 */
class AQuestionAboutOnePositionIsAnsweredByThePartWeighingItTest {

    private static final Map<String, NumberSpace> SPACING = Map.of(
            "a", NumberSpace.spacedOnly(Granularity.DISCRETE),
            "b", NumberSpace.spacedOnly(Granularity.DISCRETE),
            "x", NumberSpace.spacedOnly(Granularity.DISCRETE),
            "y", NumberSpace.spacedOnly(Granularity.DISCRETE));

    /** {@code a - b <= 0} and {@code a >= 1} apart from {@code x >= 2}, {@code x <= 9} and
     *  {@code x + y <= 12}: two parts that share no position. */
    private static NumericDomain<String> twoParts(ClosedStates closing) {
        Map<String, ExactRatio> aBelowB = new LinkedHashMap<>();
        aBelowB.put("a", ExactRatio.ONE);
        aBelowB.put("b", ExactRatio.ONE.negated());
        Map<String, ExactRatio> sum = new LinkedHashMap<>();
        sum.put("x", ExactRatio.ONE);
        sum.put("y", ExactRatio.ONE);
        return NumericDomain.top(CanonicalOrder.asTheyAreSpelled(), closing)
                .assume(new LinearForm<>(ExactRatio.ZERO, aBelowB), Rel.LE, SPACING)
                .assume(LinearForm.atomMinusConstant("a", ExactRatio.of(1)), Rel.GE, SPACING)
                .assume(LinearForm.atomMinusConstant("x", ExactRatio.of(2)), Rel.GE, SPACING)
                .assume(LinearForm.atomMinusConstant("x", ExactRatio.of(9)), Rel.LE, SPACING)
                .assume(new LinearForm<>(ExactRatio.of(-12), sum), Rel.LE, SPACING);
    }

    private static LinearForm<String> twiceAndTwo(String position) {
        return new LinearForm<>(ExactRatio.of(2), Map.of(position, ExactRatio.of(2)));
    }

    @Test
    void aQuestionAboutOnePositionPutsNoPartsTogether() {
        NumericDomain<String> domain = twoParts(ClosedStates.kept());
        long before = ClosedState.productsMade();

        assertEquals(false, domain.isBottom());
        domain.projectionOf("a");
        domain.projectionOf("x");
        domain.projectionOf(twiceAndTwo("b"));
        domain.projectionOf(twiceAndTwo("y"));
        domain.entails(LinearForm.atomMinusConstant("x", ExactRatio.of(10)), Rel.LE);
        domain.refutes(LinearForm.atomMinusConstant("a", ExactRatio.of(0)), Rel.LE);
        domain.endsAreWrittenExactly("y");

        assertEquals(before, ClosedState.productsMade(),
                "a question about one position put the parts together");
    }

    @Test
    void aQuestionSpanningThePartsPutsThemTogetherAndIsAnsweredAlike() {
        NumericDomain<String> parted = twoParts(ClosedStates.kept());
        NumericDomain<String> inOneRun = twoParts(ClosedStates.IN_ONE_RUN);
        LinearForm<String> across = new LinearForm<>(ExactRatio.ZERO,
                Map.of("a", ExactRatio.ONE, "x", ExactRatio.ONE));
        long before = ClosedState.productsMade();

        assertEquals(inOneRun.projectionOf(across), parted.projectionOf(across));

        assertTrue(ClosedState.productsMade() > before,
                "a question over two parts was answered without putting them together");
    }

    @Test
    void whatOnePositionIsLeftIsWhatTheRulesInOneRunLeaveIt() {
        NumericDomain<String> parted = twoParts(ClosedStates.kept());
        NumericDomain<String> inOneRun = twoParts(ClosedStates.IN_ONE_RUN);

        for (String position : new String[] {"a", "b", "x", "y"}) {
            assertEquals(inOneRun.projectionOf(position), parted.projectionOf(position), position);
            assertEquals(inOneRun.projectionOf(twiceAndTwo(position)),
                    parted.projectionOf(twiceAndTwo(position)), position);
        }
        assertEquals(inOneRun.projectionCertification(), parted.projectionCertification());
    }
}
