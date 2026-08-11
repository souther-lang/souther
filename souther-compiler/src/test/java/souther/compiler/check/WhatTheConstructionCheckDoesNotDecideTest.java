package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.Located;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Types with no value that the construction check admits.
 *
 * <p>The check walks for a recursion with nowhere to stop. That is not the same question as whether a
 * type has a value: it is the part of it a walk can answer, and the two come apart wherever deciding
 * an occurrence needs an answer about a whole type rather than about the position.
 *
 * <p>Held as passing tests of what happens today, because the alternative is worse in both
 * directions. Left unwritten, the gaps are indistinguishable from cases nobody thought of, and the
 * next reader takes the check for an inhabitance judgement. Written as failures, they would be
 * expectations of behaviour nothing implements, and the suite would be red for as long as that
 * stayed true.
 *
 * <p>Each of these compiles and has no value. Closing any of them means an inhabitance judgement over
 * the type graph rather than a walk from one declaration, and these become refusals.
 */
class WhatTheConstructionCheckDoesNotDecideTest {

    private static void admitted(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        assertEquals(List.of(), compilation.diagnostics().values().stream()
                        .flatMap(List::stream).map(Located::diagnostic).map(each -> each.code())
                        .toList(),
                "still admitted -- a walk cannot answer this one");
    }

    /**
     * A sum is where a cycle may bottom out in a case the walk did not come through, so the walk
     * stops at one. Where every case recurses there is no such case, and the sum has no value.
     *
     * <p>Answering it means asking each case in turn and taking the disjunction, which is a judgement
     * about the sum rather than a step along a path.
     */
    @Test
    void aSumWhoseEveryCaseHoldsTheSumHasNoValueAndIsAdmitted() {
        admitted("""
                module demo

                data Leaf = { s: Shape }
                data Branch = { s: Shape }
                data Shape = Leaf | Branch
                """);
    }

    /** And where the cycle runs out through a record and back in through the sum, which is the same
     * gap one step further along. */
    @Test
    void aCycleRoutedThroughASumIsAdmitted() {
        admitted("""
                module demo

                data Leaf = { t: Trunk }
                data Branch = { t: Trunk }
                data Shape = Leaf | Branch

                data Trunk = { s: Shape }
                """);
    }

    /**
     * A set of two needs two values of its element that differ, and the walk asks only whether the
     * element has one. Here {@code One} is bounded to a single number, so the set can never be
     * filled.
     *
     * <p>What the walk reads is a floor on how many the collection holds. How many distinct values
     * the element has is a different count, and nothing derives it.
     */
    @Test
    void aSetAskingForMoreValuesThanItsElementHasIsAdmitted() {
        admitted("""
                module demo

                data One = Int
                    invariant only = value >= 1 && value <= 1

                data Pair = Set<One>
                    invariant two = Set.size(value) >= 2
                """);
    }
}
