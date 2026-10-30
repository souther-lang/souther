package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.BlockReason;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A walk over a list written out is read element by element only within the figures of
 * {@link CompositionBudget}; past either the comparison stops at the walk, and what is said of
 * that is the figure it was declined at. A call the arithmetic has no rule for is still one it has
 * no rule for.
 */
class AListWrittenOutPastAFigureNamesTheFigureTest {

    private static final String SOURCE = """
            module g

            data Yes
            data No

            behavior classify : (n: Int, k: Int) -> Yes | No
            let classify (n, k) = if %s then Yes else No
            """;

    /** A walk adding up a list of {@code elements} written out. */
    private static String walkOver(int elements) {
        return "List.fold((acc, x) -> acc + x, 0, [n" + ", 1".repeat(elements - 1) + "])";
    }

    private static boolean stopped(ComparisonReadings.Reading only, ReadComparisons read) {
        return AffineReading.read(
                ((ComparisonReadings.Stated.AComparison) only.statement()).comparison(),
                only.reads(), read.inputs().reading(read.rules()))
                instanceof AffineReading.OfAComparison.Stopped;
    }

    /** What is said at each place the rule of {@code condition} is filed at, empty where the
     *  arithmetic reads it to the end. */
    private static List<BlockReason.RuleReadingStopped> saidOf(String condition) {
        ReadComparisons read =
                ReadComparisons.ofTheAnalysis(SOURCE.formatted(condition), "classify");
        ComparisonReadings.Reading only = read.only();
        List<BlockReason.RuleReadingStopped> said = new ArrayList<>();
        if (stopped(only, read)
                && only.standing() instanceof BoundaryPolicy.Standing.Admitted(var assessment)) {
            assessment.whatEachPlaceIsLeftWith().forEach(each -> {
                if (each.why() instanceof BlockReason.RuleReadingStopped stop) {
                    said.add(stop);
                }
            });
        }
        return said;
    }

    private static void assertNames(BlockReason.WhatItStatesIsNoLine.Why figure,
                                    List<BlockReason.RuleReadingStopped> said) {
        assertFalse(said.isEmpty(), "the reading stopped");
        assertTrue(said.stream().allMatch(each -> each
                instanceof BlockReason.WhatItStatesIsNoLine(var why) && why == figure),
                said::toString);
    }

    @Test
    void aListWithinTheFigureIsReadElementByElement() {
        int most = CompositionBudget.READINGS_OF_ONE_CONDITION.maximum();
        assertEquals(List.of(), saidOf(walkOver(most) + " >= k"));
    }

    @Test
    void aListPastTheFigureOfOneListNamesIt() {
        int most = CompositionBudget.READINGS_OF_ONE_CONDITION.maximum();
        assertNames(BlockReason.WhatItStatesIsNoLine.Why.MORE_READINGS_THAN_ARE_MADE,
                saidOf(walkOver(most + 1) + " >= k"));
    }

    @Test
    void listsPastTheFigureOfAllNameIt() {
        int each = CompositionBudget.READINGS_OF_ONE_CONDITION.maximum();
        int all = CompositionBudget.TOTAL_READINGS_OF_ONE_CONDITION.maximum();
        List<String> within = new ArrayList<>();
        for (int left = all; left > 0; left -= each) {
            within.add(walkOver(Math.min(each, left)));
        }
        assertEquals(List.of(), saidOf(String.join(" + ", within) + " >= k"),
                "as many elements in all as are read are read");
        within.add(walkOver(1));
        assertNames(BlockReason.WhatItStatesIsNoLine.Why.MORE_TOTAL_READINGS_THAN_ARE_MADE,
                saidOf(String.join(" + ", within) + " >= k"));
    }

    @Test
    void aFormTheCompilerDoesNotReadIsStillReportedAsSuch() {
        List<BlockReason.RuleReadingStopped> said = saidOf("n * n >= k");
        assertFalse(said.isEmpty(), "n * n is no form");
        assertInstanceOf(BlockReason.NonAffineArithmetic.class, said.getFirst());
    }
}
