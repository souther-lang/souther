package souther.compiler.check;

import souther.compiler.Compiler;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a body of choices standing inside choices costs the reading that bounds them.
 *
 * <p>Two bounds meet here and they are not in the same unit. How far the case splits down one path
 * are opened bounds <em>readings of a body</em>
 * ({@link HowFarSplitsAreOpenedIsBoundedByWhatARereadingCostsTest}); what a choice costs is a
 * <em>reading of a form</em> per arm, which is a question put to a domain. Sharing the number
 * between them would say the two are one unit, and they are not: what the split bound is protecting
 * against is re-reading a body, and an arm is not one.
 *
 * <p>What has to hold instead is that the arms do not compound. A choice standing inside a choice is
 * a recipe standing under another, and the memo one reading keeps means each is evaluated once for
 * that reading — so nesting costs the number of the choices and not the product of their widths.
 * That is the property a shared constant would not have given and that removing the memo would take
 * away, so it is fixed here rather than described.
 *
 * <p>Read inside a fold's step, which is where nothing else bounds a choice: the region walk opens a
 * split in a value position instead, and where it does, no recipe is evaluated at all.
 */
class ChoicesInsideChoicesCostTheirNumberAndNotTheirProductTest {

    private static final String HEAD = """
            module demo

            data NonNeg = Int
                invariant value >= 0

            """;

    /** A step whose answer is {@code depth} choices one inside another, every arm of which is the
     * accumulator — so what it answers is the accumulator however deep it goes, and what changes
     * with the depth is only how many recipes stand under one another. */
    private static String nestedInAStep(int depth) {
        StringBuilder e = new StringBuilder("acc");
        for (int i = 0; i < depth; i++) {
            e = new StringBuilder("(if x > " + i + " then " + e + " else " + e + ")");
        }
        return HEAD + """
                behavior use : (xs: List<Int>) -> NonNeg
                    constructs NonNeg
                let use (xs) = NonNeg(List.fold((acc, x) -> %s, 0, xs))
                """.formatted(e);
    }

    /** Every recipe every reading of {@code module} evaluated, counted with repeats across readings
     * and without them inside one — which is what the memo makes true. */
    private static int recipesEvaluated(String module) {
        List<List<FactSubject>> watching = new ArrayList<>();
        DerivedBounds.WATCHING = watching;
        try {
            Compiler.compileWithWarnings(module);
        } finally {
            DerivedBounds.WATCHING = null;
        }
        return watching.stream().mapToInt(List::size).sum();
    }

    /**
     * The cost of one more level is the same at every depth. A reading that forgot what it had
     * derived would evaluate the arms of every choice under every arm of the one above it, and the
     * increments would double instead of holding still.
     */
    @Test
    void oneMoreLevelOfNestingCostsTheSameAtEveryDepth() {
        List<Integer> counts = new ArrayList<>();
        for (int depth = 1; depth <= 6; depth++) {
            counts.add(recipesEvaluated(nestedInAStep(depth)));
        }
        // Read as increments and not as totals: what a total says depends on everything else the
        // module derives, and what this is about is what one more level adds.
        List<Integer> steps = new ArrayList<>();
        for (int i = 1; i < counts.size(); i++) {
            steps.add(counts.get(i) - counts.get(i - 1));
        }
        assertTrue(steps.get(0) > 0, "a level costs something, or this is watching nothing: " + counts);
        for (int i = 1; i < steps.size(); i++) {
            assertEquals(steps.get(0), steps.get(i),
                    "the sixth level costs what the second did, so the arms do not compound: "
                            + counts);
        }
    }

    /** And the body it is counting is one the rule reads to the end: every arm is the accumulator,
     * so the walk answers the seed and the construction is discharged. A body the reading gave up on
     * would hold the increments still for a reason that has nothing to do with the memo. */
    @Test
    void theNestedStepIsOneTheRuleReads() {
        for (int depth = 1; depth <= 6; depth++) {
            assertTrue(Compiler.compileWithWarnings(nestedInAStep(depth)).warnings().stream()
                            .noneMatch(d -> "E2011".equals(d.code())),
                    "every arm answers the accumulator, so the answer is the seed at depth " + depth);
        }
    }
}
