package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.RuleSite;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.SourceConstruct;
import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Putting readings of one comparison together leaves each place with the reason of the first
 * reading that met it and the calls that stopped it for that reason, and nothing else.
 *
 * <p>Held as a property over every ordering of readings and not as the cases that went wrong: a
 * reading is a place, a reason and a call, and what went wrong each time was a call arriving at a
 * place or a reason it did not belong to.
 */
class PlacesStoppedTest {

    private static final FilingCoordinate A = FilingCoordinate.at(TermPath.of("a"));
    private static final FilingCoordinate B = FilingCoordinate.at(TermPath.of("b"));

    private static final BlockReason.RuleReadingStopped DERIVED =
            new BlockReason.RuleAboutADerivedValue();
    private static final BlockReason.RuleReadingStopped FORM = new BlockReason.UnreadComparisonForm();

    private static RuleSite call(int ordinal) {
        return new RuleSite.AConstructTheAuthorWrote(new SourceConstructOrigin(
                new WrittenOwner.Body("m", "b"), ordinal, 0, SourceConstruct.CALL));
    }

    /** One reading: one place, stopped for one reason, at one call. */
    private record Reading(FilingCoordinate place, BlockReason.RuleReadingStopped why,
                           RuleSite call) {

        PlacesStopped stopped() {
            LinkedHashMap<FilingCoordinate, BlockReason.RuleReadingStopped> reasons =
                    new LinkedHashMap<>();
            reasons.put(place, why);
            return PlacesStopped.of(reasons, new LinkedHashSet<>(List.of(call)));
        }
    }

    private static List<Reading> everyReading() {
        List<Reading> out = new ArrayList<>();
        for (FilingCoordinate place : List.of(A, B)) {
            for (BlockReason.RuleReadingStopped why : List.of(DERIVED, FORM)) {
                for (RuleSite call : List.of(call(1), call(2))) {
                    out.add(new Reading(place, why, call));
                }
            }
        }
        return out;
    }

    private static PlacesStopped together(List<Reading> readings) {
        PlacesStopped out = PlacesStopped.NOWHERE;
        for (Reading each : readings) {
            out = out.and(each.stopped());
        }
        return out;
    }

    /** What the property says a place is left with, worked out from the readings alone. */
    private static void assertEachPlaceIsLeftWithItsOwn(List<Reading> readings) {
        PlacesStopped result = together(readings);
        for (FilingCoordinate place : List.of(A, B)) {
            List<Reading> here = readings.stream().filter(each -> each.place().equals(place))
                    .toList();
            if (here.isEmpty()) {
                assertEquals(Set.of(), result.sentTo(place), "nothing met " + place);
                continue;
            }
            BlockReason.RuleReadingStopped first = here.getFirst().why();
            Set<RuleSite> calls = new LinkedHashSet<>();
            here.stream().filter(each -> BlockReason.factOf(each.why())
                    .equals(BlockReason.factOf(first))).forEach(each -> calls.add(each.call()));
            assertEquals(first, result.reasons().get(place),
                    () -> "the first reading to meet " + place + " decides its reason: " + readings);
            assertEquals(calls, result.sentTo(place),
                    () -> place + " is sent to the calls that stopped it for that reason and to"
                            + " no other: " + readings);
        }
    }

    /** Every ordering of up to three readings out of all the ways a place, a reason and a call
     *  can be paired. */
    @Test
    void whateverOrderReadingsAreMetInEachPlaceKeepsOnlyTheCallsOfItsOwnReason() {
        List<Reading> all = everyReading();
        for (Reading one : all) {
            assertEachPlaceIsLeftWith(List.of(one));
            for (Reading two : all) {
                assertEachPlaceIsLeftWith(List.of(one, two));
                for (Reading three : all) {
                    assertEachPlaceIsLeftWith(List.of(one, two, three));
                }
            }
        }
    }

    private static void assertEachPlaceIsLeftWith(List<Reading> readings) {
        assertEachPlaceIsLeftWithItsOwn(readings);
    }

    /** A place no reading stopped at is sent to the rule, whatever stopped the places beside it. */
    @Test
    void aPlaceNoReadingStoppedAtIsSentToNoCall() {
        PlacesStopped stopped = new Reading(A, DERIVED, call(1)).stopped();
        LinkedHashMap<FilingCoordinate, BlockReason.RuleReadingStopped> more =
                new LinkedHashMap<>();
        more.put(A, FORM);
        more.put(B, FORM);

        PlacesStopped also = stopped.alsoFiledAt(more);

        assertEquals(Set.of(call(1)), also.sentTo(A));
        assertEquals(Set.of(), also.sentTo(B));
        assertEquals(DERIVED, also.reasons().get(A), "a place already answered keeps its answer");
        assertEquals(FORM, also.reasons().get(B));
    }
}
