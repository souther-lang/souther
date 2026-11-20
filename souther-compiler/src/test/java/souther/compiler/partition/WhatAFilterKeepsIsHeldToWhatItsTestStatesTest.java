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
 * An element a filter kept is one its test held of, so what the test states of it holds of the
 * numbers a step over the kept elements works out: {@code x + 1} over what {@code y < 100} kept
 * ends no run. What the test states is asked of the one reading of a condition, so a denial and
 * statements held together are read as it reads them, and one of two statements either of which
 * may hold says nothing of every kept element.
 */
class WhatAFilterKeepsIsHeldToWhatItsTestStatesTest {

    /** Whether working out the left side of the one comparison against {@code k}, where a step
     *  adds one to each element {@code test} keeps of {@code ds}, ends no run. */
    private static boolean aStepOverWhatItKeepsEndsNoRun(String test) {
        ReadComparisons read = ReadComparisons.ofTheAnalysis("""
                module w1
                behavior m : (ds: List<Int>, k: Int) -> Bool
                let m (ds, k) = List.length(List.map(x -> x + 1, List.filter(y -> %s, ds))) >= k
                """.formatted(test), "m");
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
    void whatATestKeepsBelowABoundEndsNoRun() {
        assertTrue(aStepOverWhatItKeepsEndsNoRun("100 > y"));
    }

    @Test
    void whatATestKeepsAboveABoundMayEndOne() {
        assertFalse(aStepOverWhatItKeepsEndsNoRun("y > 0"));
    }

    @Test
    void bothOfTwoStatementsHeldTogetherHold() {
        assertTrue(aStepOverWhatItKeepsEndsNoRun("y > 0 && y < 100"));
    }

    @Test
    void aStatementDeniedHoldsWhereItDoesNot() {
        assertTrue(aStepOverWhatItKeepsEndsNoRun("Bool.not(y >= 100)"));
    }

    @Test
    void oneOfTwoStatementsSaysNothingOfEveryKeptElement() {
        assertFalse(aStepOverWhatItKeepsEndsNoRun("y < 100 || y > 200"));
    }
}
