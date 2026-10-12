package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Text;
import souther.compiler.numeric.Towards;

import java.util.EnumSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a value stops or starts being one of a set is every place the set says it turns at: the
 * ends of a run, and each value singled out or taken out of it.
 *
 * <p>Held as the property and not as each set's answer. A value taken out of a run is inside the
 * run's extent, so a reader of the extent alone chose values either side of the run's ends and
 * none either side of the hole — and offered the hole itself as a member.
 */
class WhereStandingInASetTurnsIsEveryPlaceItsMembershipChangesTest {

    private static final int FAR = 12;

    private static final List<NumericSet> SETS = List.of(
            new NumericSet.At(Count.of(3)),
            new NumericSet.AwayFrom(List.of(Count.of(-2), Count.of(5))),
            new NumericSet.InARun(run(1, true, 4, false)),
            new NumericSet.InARunExcept(run(-3, false, 6, true),
                    List.of(Count.of(0), Count.of(2))));

    @Test
    void wheneverTwoNeighboursAreOnEitherSideOfTheSetOneOfThemIsAPlaceItTurnsAt() {
        for (NumericSet set : SETS) {
            List<Place> turns = set.turnsAt();
            for (int k = -FAR; k < FAR; k++) {
                Count here = Count.of(k);
                Count next = Count.of(k + 1);
                if (set.holds(here, Carrier.WHOLE) != set.holds(next, Carrier.WHOLE)) {
                    int at = k;
                    assertTrue(turns.stream().anyMatch(t -> t.sameAs(here) || t.sameAs(next)),
                            () -> set + " holds one of " + at + " and " + (at + 1)
                                    + " and not the other, and turns at " + turns);
                }
            }
        }
    }

    /**
     * A string away from the empty one is any other, and every other is above it: there is such a
     * string, and it is not one this invents. The run is said to hold values nothing named, so
     * composing nothing there is this compiler's reach and not the model's answer.
     */
    @Test
    void aRunOfStringsNothingNamesAValueInIsSaidAndNotLeftEmpty() {
        NumericSet awayFromEmpty = new NumericSet.AwayFrom(List.of(Text.of("")));
        Set<CompositionRepertoire> unnamed = EnumSet.noneOf(CompositionRepertoire.class);

        List<Place> chosen = CardinalityComposer.valuesAlongAnOrder(Carrier.TEXT,
                NumericDomain.Bounds.OPEN, awayFromEmpty.turnsAt(), 1, unnamed);

        assertTrue(chosen.stream().anyMatch(each -> each.sameAs(Text.of(""))),
                () -> "the place the set turns at is offered: " + chosen);
        assertEquals(Set.of(CompositionRepertoire.PLACES_IN_A_RUN_THAT_ARE_NAMED), unnamed,
                () -> "and the run above it, which no value was named in, is said: " + chosen);
    }

    private static Band run(long low, boolean lowIn, long high, boolean highIn) {
        return new Band(Band.endAt(null, Bound.at(at(low), lowIn), Towards.ABOVE),
                Band.endAt(null, Bound.at(at(high), highIn), Towards.BELOW));
    }

    private static Level at(long value) {
        return new Level.OnACarrier(Carrier.WHOLE, Count.of(value));
    }
}
