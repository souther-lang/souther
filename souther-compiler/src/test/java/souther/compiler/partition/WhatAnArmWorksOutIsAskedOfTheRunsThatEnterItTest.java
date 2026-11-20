package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import souther.compiler.check.StatedComparison;
import souther.compiler.core.Core;
import souther.compiler.inputs.Denotation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What an arm works out is worked out only by the runs that enter it, so what entering it states
 * holds of the numbers those runs work out: {@code n - 1} on the arm {@code n > 5} ends no run.
 * What was worked out before the arm was entered is worked out by every run, whichever arm it then
 * takes, and the arm says nothing of it.
 */
class WhatAnArmWorksOutIsAskedOfTheRunsThatEnterItTest {

    /** Whether working out the left side of the one comparison against {@code k} {@code body}
     *  writes, over {@code n}, ends no run, asked as a reading that passed it over asks. The
     *  conditions of the arms are comparisons of their own and are not asked. */
    private static boolean theLeftSideEndsNoRun(String body) {
        ReadComparisons read = ReadComparisons.ofTheAnalysis("""
                module w1
                behavior m : (n: Int, k: Int) -> Bool
                let m (n, k) = %s
                """.formatted(body), "m");
        List<ComparisonReadings.Reading> againstK = read.comparisons().stream()
                .filter(each -> each.statement()
                        instanceof ComparisonReadings.Stated.AComparison compared
                        && Core.withoutStanding(compared.comparison().right())
                                instanceof Core.Read name && name.name().equals("k"))
                .toList();
        assertEquals(1, againstK.size(), () -> "one comparison against k: " + read.comparisons());
        ComparisonReadings.Reading only = againstK.getFirst();
        StatedComparison stated =
                ((ComparisonReadings.Stated.AComparison) only.statement()).comparison();
        return WorkedOutToReachIt.of(read.inputs().reading(read.rules()))
                .endsNoRunWhereItWasPassedOver(new Denotation(stated.left(), only.reads()));
    }

    @Test
    void anOperationTheConditionOfItsArmKeepsWithinItsTypeEndsNoRun() {
        assertTrue(theLeftSideEndsNoRun("(if n > 5 then n - 1 else 3) >= k"));
    }

    @Test
    void theSameOperationOnTheOtherArmMayEndOne() {
        assertFalse(theLeftSideEndsNoRun("(if n > 5 then 3 else n - 1) >= k"));
    }

    @Test
    void aValueBoundBeforeTheArmIsWorkedOutOnEveryRun() {
        assertFalse(theLeftSideEndsNoRun("{ let x = n + 1 \n (if n < 0 then x else 0) >= k }"));
    }

    @Test
    void aValueBoundOnTheArmIsWorkedOutOnlyByTheRunsThatEnterIt() {
        assertTrue(theLeftSideEndsNoRun(
                "(if n > 5 then { let x = n - 1 \n x } else 3) >= k"));
    }

    @Test
    void anArmNoRunEntersWithTheOneAboveItEndsNoRun() {
        assertTrue(theLeftSideEndsNoRun(
                "(if n > 5 then (if n < 3 then n + 1 else 0) else 0) >= k"));
    }

    @Test
    void whatANameComesToOnAnArmIsNotWhatItComesToBesideIt() {
        assertFalse(theLeftSideEndsNoRun(
                "{ let p = Int.max(n, 0) \n Int.max(if n < 5 then p + 1 else 0, p + 1) >= k }"));
    }
}
