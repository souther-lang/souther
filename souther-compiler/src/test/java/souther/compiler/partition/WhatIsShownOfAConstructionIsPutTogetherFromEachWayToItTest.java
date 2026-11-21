package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.partition.ConstructionStopAssessment.ByAWay;
import souther.compiler.partition.ConstructionStopAssessment.Together;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What is shown of a construction a run may get to by several ways is put together from what each
 * way shows: a stop is a run that stops, so one way showing it is enough; that no run stops is
 * said of every run, so it takes every way, each showing it, and every way being read.
 */
class WhatIsShownOfAConstructionIsPutTogetherFromEachWayToItTest {

    private static Together together(boolean everyWay, ByAWay... each) {
        return ConstructionStopAssessment.together(each.length, at -> each[at], everyWay);
    }

    @Test
    void safeOnlyWhereEveryWayIsReadAndShowsIt() {
        assertEquals(new Together.NoneStops(), together(true, ByAWay.SAFE, ByAWay.SAFE));
        assertEquals(new Together.ByAWayNotRead(), together(false, ByAWay.SAFE, ByAWay.SAFE));
        assertEquals(new Together.NoneStops(), together(true));
        assertEquals(new Together.ByAWayNotRead(), together(false));
    }

    @Test
    void aStopShownByOneWayIsAStopWhateverTheOthersShow() {
        assertEquals(new Together.ByOne(1), together(true, ByAWay.SAFE, ByAWay.STOPS));
        assertEquals(new Together.ByOne(0), together(true, ByAWay.STOPS, ByAWay.NOT_RESOLVED));
        assertEquals(new Together.ByOne(1), together(true, ByAWay.NOT_RESOLVED, ByAWay.STOPS));
        assertEquals(new Together.ByOne(1), together(false, ByAWay.SAFE, ByAWay.STOPS));
    }

    @Test
    void notResolvedWhereNoWayShowsAStopAndOneDoesNotResolveIt() {
        assertEquals(new Together.ByOne(1), together(true, ByAWay.SAFE, ByAWay.NOT_RESOLVED));
        assertEquals(new Together.ByOne(0),
                together(true, ByAWay.NOT_RESOLVED, ByAWay.NOT_RESOLVED));
    }

    @Test
    void noWayPastAStopIsAsked() {
        List<Integer> asked = new ArrayList<>();
        ByAWay[] each = {ByAWay.SAFE, ByAWay.STOPS, ByAWay.NOT_RESOLVED};
        ConstructionStopAssessment.together(each.length, at -> {
            asked.add(at);
            return each[at];
        }, true);
        assertEquals(List.of(0, 1), asked);
    }
}
