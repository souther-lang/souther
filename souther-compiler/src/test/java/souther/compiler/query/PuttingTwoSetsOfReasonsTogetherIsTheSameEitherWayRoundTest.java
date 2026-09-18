package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Citation;
import souther.compiler.diag.SourcePos;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.Target;

import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Putting two sets of the reasons a compilation is weaker than it might be together.
 *
 * <p>What comes out is keyed by the fact each reason is about, and two reasons about one fact come
 * to the same thing whichever of them was folded first: the ones that hold evidence put their
 * citations together, and the rest hold nothing but the fact and are the same value already. So
 * which side is walked first settles nothing — and laying the two sides out end to end to fold
 * them made an order out of sets that have none, which nothing that holds one can see.
 */
class PuttingTwoSetsOfReasonsTogetherIsTheSameEitherWayRoundTest {

    @Test
    void theSideItIsFoldedFromFirstSettlesNothing() {
        WeakeningSet one = WeakeningSet.of(
                new Weakening.BodiesNotElaborated("demo.a"),
                metAt(new SourcePos(1, 0)));
        WeakeningSet other = WeakeningSet.of(
                new Weakening.BodiesNotElaborated("demo.b"),
                metAt(new SourcePos(2, 0)));

        assertEquals(one.union(other), other.union(one),
                "two sets of reasons put together are the same either way round");
        assertEquals(3, one.union(other).causes().size(),
                "and the reason both sides hold arrives once");
        assertEquals(2, one.union(other).causes().stream()
                        .filter(each -> each instanceof Weakening.ObservationIncomplete)
                        .map(each -> ((Weakening.ObservationIncomplete) each).met().citations()
                                .size())
                        .findFirst().orElse(0),
                "cited at both the places either side met it");
    }

    /** One fact of one module, met at {@code where} — so two of these are one fact cited twice. */
    private static Weakening.ObservationIncomplete metAt(SourcePos where) {
        return Weakening.ObservationIncomplete.of(
                new Incompleteness(Incompleteness.Code.OBSERVATION_ABSENT,
                        new Target.OfModule("example"), Optional.of(Citation.of(where))));
    }
}
