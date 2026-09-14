package souther.compiler.numeric;

import org.junit.jupiter.api.Test;


import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The hypothesis about how values are spaced is asked of positions the rules relate, and of no
 * others.
 *
 * <p>What the hypothesis is for is the step from "the ranges and the relations between them are the
 * feasible set" to "each range is the whole of what the rules leave that position", and that step is
 * taken through the relations. So a position and everything a chain of relations reaches from it
 * have to be of one kind, and two positions no rule mentions together do not — they are two systems
 * that happen to be written down beside each other, which is what a record with a whole number in
 * one field and a decimal in another is.
 *
 * <p>No source the checker accepts reaches the refusing case today: a comparison of a whole number
 * against a decimal does not get through the types, so the rules never relate two positions of
 * different kinds. Asked here rather than through a declaration for that reason — and asked at all
 * because what keeps it out is the checker and not this theorem, and the two are free to move apart.
 */
class TheClosureTheoremIsAskedOfPositionsTheRulesRelateTest {

    private static final ProjectionCertification CERTIFIED =
            new ProjectionCertification.Certified(
                    new ProjectionCertificate.ByBoxAndClosedDifferences());

    /** The refusal this is about, asked for by name rather than as the absence of a certificate. */
    private static final ProjectionCertification SPACED_DIFFERENTLY =
            new ProjectionCertification.PositionsSpacedDifferently();

    /** Two kinds in one value, related by nothing, is two systems and both are certified. */
    @Test
    void positionsNoRuleRelatesAreNotHeldToOneKind() {
        NumericDomain<String> domain = bounded(Map.of(
                "whole", Granularity.DISCRETE, "part", Granularity.DENSE));

        assertEquals(CERTIFIED, domain.projectionCertification());
    }

    /** A rule relating them makes them one system, and the theorem is not about a mixed one. */
    @Test
    void aRuleRelatingTwoKindsIsNotCertified() {
        NumericDomain<String> domain = relating(
                Map.of("whole", Granularity.DISCRETE, "part", Granularity.DENSE),
                "whole", "part");

        assertEquals(SPACED_DIFFERENTLY, domain.projectionCertification());
    }

    /** And the same relation between two positions of one kind is. */
    @Test
    void aRuleRelatingOneKindIsCertified() {
        NumericDomain<String> domain = relating(
                Map.of("whole", Granularity.DISCRETE, "other", Granularity.DISCRETE),
                "whole", "other");

        assertEquals(CERTIFIED, domain.projectionCertification());
    }

    /**
     * Reached through a chain, because the closure composes edges.
     *
     * <p>Nothing here relates the whole number to the decimal. Closing the two differences leaves a
     * relation between them that nobody wrote, and it is the same mixture one composition further
     * on.
     */
    @Test
    void twoKindsReachingEachOtherThroughAThirdPositionAreNotCertified() {
        Map<String, Granularity> kinds = new LinkedHashMap<>();
        kinds.put("whole", Granularity.DISCRETE);
        kinds.put("between", Granularity.DISCRETE);
        kinds.put("part", Granularity.DENSE);
        NumericDomain<String> domain = relating(kinds, "whole", "between");
        domain = domain.assume(difference("between", "part"), Rel.LE, kinds);

        assertEquals(SPACED_DIFFERENTLY, domain.projectionCertification());
    }

    // --- the systems ------------------------------------------------------------------------------

    /** Every position bounded on its own, which is a system every certificate holds of. */
    private static NumericDomain<String> bounded(Map<String, Granularity> kinds) {
        NumericDomain<String> domain = NumericDomain.top();
        for (String position : kinds.keySet()) {
            domain = domain.assume(
                    LinearForm.<String>atom(position), Rel.GE, kinds);
            domain = domain.assume(
                    LinearForm.<String>atom(position).minus(num(7)), Rel.LE, kinds);
        }
        return domain;
    }

    /** The same, with one difference written between two of the positions. */
    private static NumericDomain<String> relating(Map<String, Granularity> kinds,
                                                  String above, String below) {
        return bounded(kinds).assume(difference(above, below), Rel.LE, kinds);
    }

    /** {@code above - below <= 2}, which the difference bounds hold in full. */
    private static LinearForm<String> difference(String above, String below) {
        return LinearForm.<String>atom(above)
                .minus(LinearForm.<String>atom(below))
                .minus(num(2));
    }

    private static LinearForm<String> num(long n) {
        return LinearForm.constant(BigDecimal.valueOf(n));
    }
}
