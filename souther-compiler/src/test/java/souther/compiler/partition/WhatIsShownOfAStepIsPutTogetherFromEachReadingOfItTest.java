package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.partition.WhatEveryWayShows.Shown;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What is shown of a step read several ways — each way to it, each application, each way of its
 * values, each kind of site — is put together from what each reading shows: a stop is a run that
 * stops, so one reading showing it is enough; that no run stops is said of every run, so it
 * takes every reading, each showing it, and every reading there is being read. Whether a run
 * stops does not turn on the order the readings are asked in.
 */
class WhatIsShownOfAStepIsPutTogetherFromEachReadingOfItTest {

    /** What the readings {@code each} show together: what one of them shows, or
     *  {@code "not every way"} or {@code "no way"}. */
    private static String together(boolean every, Shown... each) {
        return WhatEveryWayShows.together(each.length, at -> each[at] + "#" + at,
                judged -> Shown.valueOf(judged.substring(0, judged.indexOf('#'))), every,
                () -> "not every way", () -> "no way");
    }

    /** The same, without which reading it was. */
    private static String shown(boolean every, List<Shown> each) {
        String judged = together(every, each.toArray(Shown[]::new));
        return judged.contains("#") ? judged.substring(0, judged.indexOf('#')) : judged;
    }

    @Test
    void safeOnlyWhereEveryReadingIsReadAndShowsIt() {
        assertEquals("SAFE#0", together(true, Shown.SAFE, Shown.SAFE));
        assertEquals("not every way", together(false, Shown.SAFE, Shown.SAFE));
        assertEquals("no way", together(true));
        assertEquals("not every way", together(false));
    }

    @Test
    void aStopShownByOneReadingIsAStopWhateverTheOthersShow() {
        assertEquals("STOPS#1", together(true, Shown.SAFE, Shown.STOPS));
        assertEquals("STOPS#0", together(true, Shown.STOPS, Shown.NOT_RESOLVED));
        assertEquals("STOPS#1", together(true, Shown.NOT_RESOLVED, Shown.STOPS));
        assertEquals("STOPS#1", together(false, Shown.SAFE, Shown.STOPS));
    }

    @Test
    void notResolvedWhereNoReadingShowsAStopAndOneDoesNotResolveIt() {
        assertEquals("NOT_RESOLVED#1", together(true, Shown.SAFE, Shown.NOT_RESOLVED));
        assertEquals("NOT_RESOLVED#0", together(true, Shown.NOT_RESOLVED, Shown.SAFE));
        assertEquals("NOT_RESOLVED#0", together(true, Shown.NOT_RESOLVED, Shown.NOT_RESOLVED));
    }

    /** Every order of every list of up to three readings, each of every kind, shows the same. */
    @Test
    void whatIsShownDoesNotTurnOnTheOrderTheReadingsAreAskedIn() {
        List<List<Shown>> lists = new ArrayList<>();
        lists.add(List.of());
        for (int size = 1; size <= 3; size++) {
            List<List<Shown>> longer = new ArrayList<>();
            for (List<Shown> each : lists) {
                if (each.size() == size - 1) {
                    for (Shown one : Shown.values()) {
                        List<Shown> more = new ArrayList<>(each);
                        more.add(one);
                        longer.add(more);
                    }
                }
            }
            lists.addAll(longer);
        }
        for (List<Shown> each : lists) {
            for (boolean every : List.of(true, false)) {
                List<Shown> reversed = new ArrayList<>(each);
                Collections.reverse(reversed);
                List<Shown> rotated = new ArrayList<>(each);
                Collections.rotate(rotated, 1);
                assertEquals(shown(every, each), shown(every, reversed), each + " " + every);
                assertEquals(shown(every, each), shown(every, rotated), each + " " + every);
            }
        }
    }

    @Test
    void noReadingPastAStopIsAsked() {
        List<Integer> asked = new ArrayList<>();
        Shown[] each = {Shown.SAFE, Shown.STOPS, Shown.NOT_RESOLVED};
        WhatEveryWayShows.together(each.length, at -> {
            asked.add(at);
            return each[at];
        }, judged -> judged, true, () -> Shown.NOT_RESOLVED, () -> Shown.SAFE);
        assertEquals(List.of(0, 1), asked);
    }
}
