package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.AReadingOfAPosition;
import souther.compiler.check.Carrier;
import souther.compiler.check.NarrowedBounds;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A quantity the rules leave one value stops there both ways, and its two ends keep their own names.
 *
 * <p>The case the side is carried for. Everything downstream of the reading compares places: the end
 * lowers onto the value the quantity takes, and a run is held to the place it reaches
 * ({@link Bound#canonical()}). At one value the low end and the high end lower onto one place, so
 * every one of those comparisons answers the same for both — and a reader that had only the place
 * would answer the low end's question with the high end's names.
 *
 * <p>Which is why this is asked here and not where the reading is. That
 * {@code NarrowedBounds.matching} tells the two apart is
 * {@code ARangeStoppingAtOneValueStillHasTwoEndsTest}; that the answer is still told apart after it
 * has been lowered and matched against where a run reaches is this. Written only at the reading, the
 * side could be dropped anywhere below it and every other test of this change would still pass.
 */
class TheTwoEndsOfOneValueKeepTheirOwnNarrowingTest {

    private static final Carrier WHOLE = new Carrier.Whole();
    private static final TypeSymbol.AtModule FLOOR = named("Floor");
    private static final TypeSymbol.AtModule CEILING = named("Ceiling");

    /** Where the rules leave the quantity: the one value three, held from below and from above by
     *  two different declarations. */
    private static final NumericDomain.Bounds ONE_VALUE =
            new NumericDomain.Bounds(at(3), at(3));

    @Test
    void theLowEndIsOwedToWhatHoldsItAndNotToWhatHoldsTheHighOne() {
        QuantityArrangement.Run run = theOneRun(AReadingOfAPosition.withBothEndsAt(
                at(3), List.of(FLOOR), List.of(CEILING)));

        assertEquals(List.of(FLOOR), narrowersOf(run.below()),
                "the run starts where Floor holds it, and Ceiling holds the other end");
        assertEquals(List.of(CEILING), narrowersOf(run.above()),
                "and stops where Ceiling holds it, at the same place");
    }

    /** And a reading that holds one of the two holds nothing at the other. */
    @Test
    void anEndTheReadingSaysNothingAboutIsOwedToNobody() {
        QuantityArrangement.Run run =
                theOneRun(AReadingOfAPosition.withAnUpperEndAt(at(3), CEILING));

        assertEquals(List.of(), narrowersOf(run.below()),
                "nothing stops it from below in that reading, and the number is no answer");
        assertEquals(List.of(CEILING), narrowersOf(run.above()));
    }

    /** The single run of a quantity nothing parts, held to the one value the rules leave it. */
    private static QuantityArrangement.Run theOneRun(NarrowedBounds narrowed) {
        LevelSpace space = LevelSpace.onACarrier(WHOLE);
        QuantityArrangement arranged = QuantityArrangement.of(space, List.of(),
                DomainEnds.leaving(space, new Level.OnACarrier(WHOLE, Count.of(3)), ONE_VALUE,
                        narrowed));
        List<QuantityArrangement.Run> runs = arranged.runs();
        assertEquals(1, runs.size(), () -> "one value, one run: " + runs);
        return runs.get(0);
    }

    /** The declarations a row inside the run is told its end is owed to. */
    private static List<TypeSymbol.AtModule> narrowersOf(List<RegionClaim> claims) {
        return claims.stream().flatMap(each -> each.contributions().narrowers().stream()).toList();
    }

    private static Endpoint at(long value) {
        return Endpoint.inclusive(Count.of(value));
    }

    private static TypeSymbol.AtModule named(String name) {
        return TypeSymbols.declared(new TypeKey("example.hold", name));
    }
}
