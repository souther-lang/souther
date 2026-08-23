package souther.compiler.check;

import souther.compiler.Compiler;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A recipe standing under several others is evaluated once for the reading that asks it.
 *
 * <p>What a reading is, is one evaluation of the recipes against one domain. So this is not a claim
 * that a body of choices costs a fixed amount: two readings against two domains evaluate the same
 * recipe twice and are right to, which is why a walk's own readings each take a memo of their own —
 * what is derived under an assumed accumulator is not what is derived without one. What is claimed
 * is that <em>within</em> a reading nothing is derived twice, which is what makes the recipes an
 * evaluation over a graph rather than over the tree of paths through it.
 *
 * <p>Measured on choices inside choices because that is where the difference shows. A choice under
 * a choice is reached once by each arm above it, so a reading that forgot what it had answered
 * would evaluate the arms of every choice under every arm of the one above — and the cost of one
 * more level would double instead of holding still.
 *
 * <p>Read inside a fold's step, which is where nothing else bounds a choice: the region walk opens a
 * split in a value position instead, and where it does, no recipe is evaluated at all. It is also
 * where the memo could stop holding unremarked, since a walk's readings are the ones nothing outside
 * could see.
 *
 * <p>Nothing here is a bound on how many readings there are, and there is no such bound to lean on.
 * How far splits are opened is a different question in a different unit — it counts re-readings of a
 * body, and an arm read is a question put to a domain — and its own policy lets the first split on a
 * path be opened however wide it is
 * ({@link HowFarSplitsAreOpenedIsBoundedByWhatARereadingCostsTest}). Measured, a match of eighty
 * cases is opened and the body is read a hundred and sixty times. So this states nothing about what
 * a whole compilation costs. What it states is that <em>this</em> adds no factor: within one reading
 * the recipes do not multiply through nested choices, whatever produced the reading.
 */
class ARecipeIsEvaluatedOnceForTheReadingThatAsksItTest {

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

    /** How many recipes were evaluated while compiling {@code module}, over every reading there was.
     * {@link DerivedNumericFacts#WATCHING} records an atom once per evaluation, so a memo that stopped
     * holding shows here and a memo that held does not. */
    private static int recipesEvaluated(String module) {
        List<List<FactSubject>> watching = new ArrayList<>();
        DerivedNumericFacts.WATCHING = watching;
        try {
            Compiler.compileWithWarnings(module);
        } finally {
            DerivedNumericFacts.WATCHING = null;
        }
        return watching.stream().mapToInt(List::size).sum();
    }

    /**
     * The cost of one more level of nesting is the same at every depth.
     *
     * <p>Which follows from the memo and from nothing else here: the readings are the same readings
     * at every depth — one per candidate range, against one domain each — and what changes is only
     * how many recipes stand under the step's own form. So a level costs its own recipes once, and
     * the increments hold still.
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
                    "the sixth level costs what the second did, so a recipe under two arms was"
                            + " evaluated for the reading and not for each arm: " + counts);
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
