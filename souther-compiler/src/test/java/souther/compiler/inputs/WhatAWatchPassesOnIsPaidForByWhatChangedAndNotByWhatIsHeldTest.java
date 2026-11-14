package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.ElementBindings;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;
import souther.test.Growth;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.SequencedMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a watch passes on and what asking it costs follow what changed between the applications
 * and the readings, and not how much each holds.
 *
 * <p>Held as how much was looked at, not as how long it takes: a set shared by many readings that
 * each hand other names on is looked at once for each of them and not once for each way to it, and
 * a reading that asked nothing of what was handed is compared with an environment holding
 * thousands of names by looking at none.
 */
class WhatAWatchPassesOnIsPaidForByWhatChangedAndNotByWhatIsHeldTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final BindingOwner OWNER = new BindingOwner.OfValue("demo", "go");
    private static final BindingId Y = new BindingId(OWNER, 0);
    private static final BindingId Z = new BindingId(OWNER, 1);
    private static final BindingId SPARE = new BindingId(OWNER, 2);

    private static BindingEnvironment nothingHanded() {
        return new BindingEnvironment(Map.of(), Map.of(), ElementBindings.NONE,
                ValueDefinitions.NONE, false);
    }

    private static Core written(long value) {
        return new Core.Int(value, Type.INT, POS);
    }

    private static BindingEnvironment holding(int names) {
        BindingEnvironment each = nothingHanded();
        for (int i = 0; i < names; i++) {
            each = each.handing(new BindingId(OWNER, 1000 + i), written(i));
        }
        return each;
    }

    /** What the counting says while {@code run} runs. */
    private static long[] counting(Runnable run) {
        long[] counting = new long[4];
        AskedNames.COUNTING = counting;
        try {
            run.run();
        } finally {
            AskedNames.COUNTING = null;
        }
        return counting;
    }

    /** The watch of the reading of {@code Y} began on {@code env}, taking in twice over what the
     *  one a step further on, which hands {@code Z}, asked: once as that reading ended and once as
     *  a reading taken again. Each of the sets so shared is reached two ways. */
    private static HandedAnswers shared(int depth, BindingEnvironment env) {
        return BindingEnvironment.Watch.over(env, () -> {
            env.roleOf(Y);
            if (depth > 0) {
                BindingEnvironment further = env.handing(Z, written(depth));
                HandedAnswers below = shared(depth - 1, further);
                BindingEnvironment.Watch.replay(further, below);
            }
            return 0;
        }).asked();
    }

    private static long worked(int depth) {
        BindingEnvironment began = nothingHanded().handing(SPARE, written(0));
        BindingEnvironment handed = began.handing(Y, written(1)).handing(Z, written(2));
        long[] counting = counting(() -> {
            HandedAnswers below = shared(depth, handed);
            BindingEnvironment.Watch.over(began, () -> {
                BindingEnvironment.Watch.replay(handed, below);
                return 0;
            });
        });
        return counting[0] + counting[1] + counting[3];
    }

    @Test
    void aSetSharedByManyReadingsWhoseNamesAreAllHandedAgainIsLookedAtOnceForEach() {
        SequencedMap<Integer, Long> looked = new LinkedHashMap<>();
        for (int depth : new int[] {6, 12}) {
            looked.put(depth, worked(depth));
        }
        Growth.eachAtMost(looked, 3, 1);
    }

    @Test
    void aReadingThatAskedNothingIsComparedWithManyNamesByLookingAtNone() {
        BindingEnvironment on = holding(20);
        BindingEnvironment other = on.handing(SPARE, written(1));
        HandedAnswers asked = BindingEnvironment.Watch.over(on, () -> 0).asked();

        long[] counting = counting(() -> assertTrue(asked.holdsOf(other)));

        assertEquals(0L, counting[1]);
    }

    @Test
    void aReadingThatAskedAFewNamesIsComparedByLookingAtWhatTheTwoApplicationsDifferOn() {
        BindingEnvironment on = holding(20).handing(Y, written(1));
        BindingEnvironment other = on.handing(Z, written(5));
        HandedAnswers asked = BindingEnvironment.Watch.over(on, () -> on.roleOf(Y)).asked();

        long[] counting = counting(() -> assertTrue(asked.holdsOf(other)));

        assertEquals(1L, counting[1], "the one step between the two, of the 21 names held");
    }

    @Test
    void aSetOfManyNamesTakenInFromDeepInsideIsPlacedByOneWalkUpTheApplications() {
        BindingEnvironment on = nothingHanded();
        BindingEnvironment deep = on;
        for (int i = 0; i < 20; i++) {
            deep = deep.handing(new BindingId(OWNER, 2000 + i), written(i));
        }
        BindingEnvironment from = deep;
        HandedAnswers asked = BindingEnvironment.Watch.over(from, () -> {
            for (int i = 0; i < 5; i++) {
                from.roleOf(new BindingId(OWNER, 3000 + i));
            }
            return 0;
        }).asked();

        long[] counting = counting(() -> BindingEnvironment.Watch.over(on, () -> {
            BindingEnvironment.Watch.replay(from, asked);
            return 0;
        }));

        assertEquals(20L, counting[3], "one walk, and not one for each of the 5 names");
        assertEquals(5L, counting[0], "the names, once, and not the steps for each of them");
    }

    @Test
    void aReadingTakenAgainFromTheSameEnvironmentAddsNothingTheSecondTime() {
        BindingEnvironment on = nothingHanded();
        BindingEnvironment since = on.handing(Z, written(1));

        long once = counting(() -> takenAgain(on, since, 1))[0];
        long twice = counting(() -> takenAgain(on, since, 2))[0];

        assertEquals(once, twice, "the second was the first again");
    }

    @Test
    void aReadingTakenAgainFromTwoEnvironmentsInTurnAddsNothingAfterTheFirstOfEach() {
        long once = counting(() -> takenAgainInTurn(1))[0];
        long twice = counting(() -> takenAgainInTurn(2))[0];

        assertEquals(once, twice, "the second round was the first again");
    }

    /** A reading that asked {@code Y} and {@code Z}, taken again from two environments that hand
     *  {@code Y} what the watch began with, one and then the other, {@code rounds} times. */
    private static void takenAgainInTurn(int rounds) {
        BindingEnvironment on = nothingHanded().handing(Y, written(1));
        BindingEnvironment one = on.handing(Y, written(1));
        BindingEnvironment other = on.handing(Y, written(1));
        HandedAnswers asked = BindingEnvironment.Watch.over(on, () -> {
            on.roleOf(Z);
            return on.roleOf(Y);
        }).asked();
        BindingEnvironment.Watch.over(on, () -> {
            for (int i = 0; i < rounds; i++) {
                BindingEnvironment.Watch.replay(one, asked);
                BindingEnvironment.Watch.replay(other, asked);
            }
            return 0;
        });
    }

    /** A reading read on {@code since}, taken again {@code times} times inside a watch on
     *  {@code on}. Made afresh for each call: what a set holds is worked out once and kept. */
    private static void takenAgain(BindingEnvironment on, BindingEnvironment since, int times) {
        HandedAnswers asked = BindingEnvironment.Watch.over(since, () -> {
            since.roleOf(Y);
            return since.roleOf(Z);
        }).asked();
        BindingEnvironment.Watch.over(on, () -> {
            for (int i = 0; i < times; i++) {
                BindingEnvironment.Watch.replay(since, asked);
            }
            return 0;
        });
    }
}
