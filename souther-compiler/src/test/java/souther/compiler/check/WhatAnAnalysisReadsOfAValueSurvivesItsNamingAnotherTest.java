package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.core.Core;
import souther.compiler.query.Bodies;
import souther.compiler.types.WrittenOwner;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What the tree an analysis reads holds of a value is what the value says, however many values it
 * is written through.
 *
 * <p>A threshold and a predicate are read off the comparison a value writes, so a tree that dropped
 * it would leave those readers a value they know the type of and nothing else. And an alias — a
 * value that is another value and nothing more — is no change to what is meant, so one more of them
 * must not change what an analysis reads.
 *
 * <p>What is read is the body and the template of every value it builds, since a value is held once
 * and the body holds where it is built.
 */
class WhatAnAnalysisReadsOfAValueSurvivesItsNamingAnotherTest {

    private static AnalysisBody analysed(String source, String behavior) {
        return Compiler.compiled(source, "m").db()
                .ask(new Bodies.Checked("m")).value().analysisBodies().get(behavior);
    }

    /** How many comparisons the definition {@code definition} wrote stand in what {@code analysis}
     *  reads: the body, and the template of each value it builds. */
    private static int comparisonsWrittenBy(AnalysisBody analysis, String definition) {
        List<Core> read = new ArrayList<>();
        read.add(analysis.core());
        read.addAll(analysis.templatesAfterTheirBuilders());
        int held = 0;
        for (Core tree : read) {
            held += comparisonsWrittenBy(tree, definition);
        }
        return held;
    }

    private static int comparisonsWrittenBy(Core e, String definition) {
        if (e == null) {
            return 0;
        }
        int[] held = {e instanceof Core.Binary b && b.origin() != null && b.origin().isWritten()
                && b.origin().owner() instanceof WrittenOwner.Body owner
                && owner.definition().equals(definition) ? 1 : 0};
        Core.forEachChild(e, child -> held[0] += comparisonsWrittenBy(child, definition));
        return held[0];
    }

    @Test
    void aValueNamingAnotherKeepsWhatItComparesWhereAnAnalysisReadsIt() {
        AnalysisBody analysis = analysed("""
                module m exposing (f)

                let base = List.length([1, 2, 3])

                let enough = base > 2

                behavior f : (n: Int) -> Int
                let f (n) = if enough then n else 0
                """, "f");

        assertEquals(1, comparisonsWrittenBy(analysis, "enough"),
                "the comparison `enough` writes is what a predicate reading `f` is read off");
    }

    @Test
    void anAliasOfAValueIsNoChangeToWhatAnAnalysisReadsOfIt() {
        AnalysisBody analysis = analysed("""
                module m exposing (f)

                let a0 = List.length([1, 2, 3]) > 2

                let a1 = a0

                let a2 = a1

                let a3 = a2

                let a4 = a3

                behavior f : (n: Int) -> Int
                let f (n) = if a4 then n else 0
                """, "f");

        assertEquals(1, comparisonsWrittenBy(analysis, "a0"),
                "however many values `a0` is written through, its comparison is what is read");
    }
}
