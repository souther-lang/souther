package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.EndSide;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Which side an end is on is asked beside the number, because the number does not always say.
 *
 * <p>A coordinate the rules leave one value stops at that value both ways, and its two ends are then
 * one end to everything that compares numbers — {@link Endpoint#sameAs} included, which is the
 * predicate that says whether two ends stop a coordinate in one spot. It is the right predicate and
 * it answers the other question: two different declarations can be holding the two ends, and asked
 * by the number alone each would come back holding both.
 *
 * <p>Which is why a caller says which end it means. Everything that carries an end onward carries
 * the side with it, down to where a name is written beside a place a run stops at.
 */
class ARangeStoppingAtOneValueStillHasTwoEndsTest {

    private static final TypeSymbol.AtModule FLOOR = named("Floor");
    private static final TypeSymbol.AtModule CEILING = named("Ceiling");

    /** One number, two ends, and a declaration apiece. */
    @Test
    void theTwoEndsOfOneValueAreHeldSeparately() {
        NarrowedBounds atThree = NarrowedBounds.of(
                new NumericDomain.Bounds(endAt(3), endAt(3)),
                List.of(FLOOR), List.of(CEILING));

        assertEquals(List.of(FLOOR), holding(atThree, EndSide.LOWER),
                "what says the values start at three is holding the low end");
        assertEquals(List.of(CEILING), holding(atThree, EndSide.UPPER),
                "and what says they stop there is holding the high one, at the same number");
    }

    /** And a side the reading stops nothing on holds nobody, whatever the other side says. */
    @Test
    void aSideWithNoEndHoldsNobodyEvenWhereTheOtherEndIsAtThatNumber() {
        NarrowedBounds cappedOnly = AReadingOfAPosition.withAnUpperEndAt(endAt(3), CEILING);

        assertEquals(List.of(CEILING), cappedOnly.matching(EndSide.UPPER, endAt(3))
                        .map(MatchedEndAttribution::names).orElseGet(List::of),
                "the high end is where this reading stops the coordinate");
        assertEquals(List.of(), cappedOnly.matching(EndSide.LOWER, endAt(3))
                        .map(MatchedEndAttribution::names).orElseGet(List::of),
                "and nothing stops it from below for anybody to be holding");
    }

    private static List<TypeSymbol.AtModule> holding(NarrowedBounds narrowed, EndSide side) {
        return AReadingOfAPosition.holding(narrowed, side);
    }

    private static Endpoint endAt(long at) {
        return Endpoint.inclusive(Count.of(at));
    }

    private static TypeSymbol.AtModule named(String name) {
        return TypeSymbols.declared(new TypeKey("example.hold", name));
    }
}
