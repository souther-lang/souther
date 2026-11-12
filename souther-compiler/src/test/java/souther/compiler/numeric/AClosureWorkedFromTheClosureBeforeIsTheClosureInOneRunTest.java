package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.RulesAsWritten.Written;
import souther.compiler.numeric.RulesNamingNoPositionInCommonCloseApartTest.Outcome;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Rules said one at a time leave, at every step, what the same rules leave closed in one run, however
 * much of each closure was worked out from the one before.
 *
 * <p>Each step is the rules so far asked of one table with the closure of the step before lent, which
 * is how a search over a path asks them: the closure of the rules with one more is worked from the
 * work of the closure it follows ({@link ClosureWork}). What is compared is everything a state
 * answers — the box, the differences both ways, what the holes came to, whether the rounds ran out
 * and whether every bound was composed — against the closure of those rules worked out alone.
 *
 * <p>A rule said after moves the ends of the positions it bounds and nothing else, which is the
 * shape the work is moved over. The premises moved are counted so that a sequence that moved none is
 * not read as one that held.
 */
class AClosureWorkedFromTheClosureBeforeIsTheClosureInOneRunTest {

    private static final List<String> POSITIONS = List.of("a", "b", "cc", "d");

    private static final int SEQUENCES = 150;

    @Test
    void everyStepOfRulesSaidOneAtATimeIsTheClosureInOneRun() {
        long[] heldAndMoved = saidOneAtATime(ClosureWork.PLACES_KEPT, SEQUENCES);
        assertTrue(heldAndMoved[0] > 500,
                "too few steps for this to hold anything: " + heldAndMoved[0]);
        assertTrue(heldAndMoved[1] > 500,
                "too few premises were moved for this to hold anything: " + heldAndMoved[1]);
    }

    /** A closure that keeps few places of its work, or none, is the closure it is with room. */
    @Test
    void aClosureKeepingLittleOfItsWorkIsTheClosureInOneRun() {
        for (long placesKept : new long[] {12, 60}) {
            saidOneAtATime(placesKept, 40);
        }
        assertEquals(0, saidOneAtATime(0, 40)[1],
                "premises were moved from work that was not kept");
    }

    @Test
    void aClosureKeepsNoMoreOfItsWorkThanItIsGivenRoomFor() {
        Random dice = new Random(316701);
        CanonicalOrder<String> order = CanonicalOrder.asTheyAreSpelled();
        long kept = 0;
        for (int sequence = 0; sequence < 40; sequence++) {
            List<AffineConstraint<String>> rules = read(someRules(dice, 6));
            ClosureWork<String> work = new ClosureWork<>(30);
            ClosedState.closedTogether(rules, RulesNamingNoPositionInCommonCloseApartTest::spacing,
                    order, null, work);
            assertTrue(work.placesKept() <= 30, "a closure kept " + work.placesKept()
                    + " places of work where it was given room for 30");
            kept += work.placesKept();
        }
        assertTrue(kept > 0, "nothing was kept, so a bound on what is kept is not asked");
    }

    /** Every step over {@code sequences} sequences, as {@code {steps, premises moved}}. */
    private static long[] saidOneAtATime(long placesKept, int sequences) {
        Random dice = new Random(316700);
        long moved = 0;
        int steps = 0;
        for (int sequence = 0; sequence < sequences; sequence++) {
            CanonicalOrder<String> order = RulesNamingNoPositionInCommonCloseApartTest.ORDERS
                    .get(sequence % RulesNamingNoPositionInCommonCloseApartTest.ORDERS.size());
            List<AffineConstraint<String>> said = read(someRules(dice, 4 + dice.nextInt(6)));
            ClosedStates kept = ClosedStates.keptWithWorkOf(placesKept);
            ClosedStates.Parted<String> before = null;
            for (int at = 1; at <= said.size(); at++) {
                List<AffineConstraint<String>> sofar = said.subList(0, at);
                before = kept.of(sofar, RulesNamingNoPositionInCommonCloseApartTest::spacing, order,
                        before);
                Outcome alone = RulesNamingNoPositionInCommonCloseApartTest.outcome(
                        ClosedState.closedTogether(sofar,
                                RulesNamingNoPositionInCommonCloseApartTest::spacing, order));
                assertEquals(alone, RulesNamingNoPositionInCommonCloseApartTest.outcome(
                        before.state()), "the rules " + sofar + " said one at a time are not "
                        + "the rules in one run");
                steps++;
            }
            moved += kept.premisesMoved();
        }
        return new long[] {steps, moved};
    }

    private static List<AffineConstraint<String>> read(List<Written> written) {
        return RulesAsWritten.statedOnly(written,
                RulesNamingNoPositionInCommonCloseApartTest::spacing);
    }

    /** Rules over the positions: bounds, differences and sums weighted unevenly, with now and then
     *  a bound a hair from the others in scale. */
    private static List<Written> someRules(Random dice, int howMany) {
        List<Written> out = new ArrayList<>();
        for (int i = 0; i < howMany; i++) {
            Map<String, ExactRatio> coefs = new LinkedHashMap<>();
            for (String position : POSITIONS) {
                int weight = dice.nextInt(7) - 3;
                if (weight != 0 && dice.nextInt(3) != 0) {
                    coefs.put(position, ExactRatio.of(weight));
                }
            }
            if (coefs.isEmpty()) {
                continue;
            }
            ExactRatio constant = dice.nextInt(8) == 0
                    ? RulesNamingNoPositionInCommonCloseApartTest.A_HAIR
                    : ExactRatio.of(dice.nextInt(21) - 10);
            Rel[] all = Rel.values();
            out.add(new Written(coefs, constant, all[dice.nextInt(all.length)]));
        }
        return out;
    }
}
