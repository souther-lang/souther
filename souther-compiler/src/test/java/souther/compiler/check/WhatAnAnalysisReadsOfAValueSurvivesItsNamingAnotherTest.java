package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.ast.Hir;
import souther.compiler.query.Bodies;
import souther.compiler.types.WrittenOwner;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the tree an analysis reads holds of a value is what the value says, however it is built.
 *
 * <p>A value that names another is not a value an analysis can be given as a reference: the
 * comparison it writes is what a threshold and a predicate are read off, and a tree that dropped it
 * would leave those readers a value they know the type of and nothing else. What is bounded is how
 * far that goes — a chain of values each naming the last, which is what a copy multiplies — and it
 * is bounded by how deep the chain is and by nothing that depends on the order anything was walked.
 */
class WhatAnAnalysisReadsOfAValueSurvivesItsNamingAnotherTest {

    private static Hir.Expr analysed(String source, String behavior) {
        return Compiler.compiled(source, "m").db()
                .ask(new Bodies.BodyForInvariantDischarge("m", behavior))
                .value().value().writtenBody();
    }

    /** How many comparisons the definition {@code definition} wrote stand in {@code e}. */
    private static int comparisonsWrittenBy(Hir.Expr e, String definition) {
        if (e == null) {
            return 0;
        }
        int[] held = {e instanceof Hir.Binary b && b.origin() != null && b.origin().isWritten()
                && b.origin().owner() instanceof WrittenOwner.Body owner
                && owner.definition().equals(definition) ? 1 : 0};
        Hir.forEachChild(e, child -> held[0] += comparisonsWrittenBy(child, definition));
        return held[0];
    }

    private static int nodes(Hir.Expr e) {
        if (e == null) {
            return 0;
        }
        int[] held = {1};
        Hir.forEachChild(e, child -> held[0] += nodes(child));
        return held[0];
    }

    @Test
    void aValueNamingAnotherKeepsWhatItComparesWhereAnAnalysisReadsIt() {
        Hir.Expr body = analysed("""
                module m exposing (f)

                let base = List.length([1, 2, 3])

                let enough = base > 2

                behavior f : (n: Int) -> Int
                let f (n) = if enough then n else 0
                """, "f");

        assertEquals(1, comparisonsWrittenBy(body, "enough"),
                "the comparison `enough` writes is what a predicate reading `f` is read off");
    }

    private static String chain(int links) {
        StringBuilder source = new StringBuilder(
                "module m exposing (f)\n\nlet a0 = List.length([1, 2, 3])\n");
        for (int i = 1; i <= links; i++) {
            String previous = "a" + (i - 1);
            source.append("let a").append(i).append(" = (if List.length([1]) > 0 then ")
                    .append(previous).append(" else 0) + (if List.length([1, 2]) > 1 then ")
                    .append(previous).append(" else 0)\n");
        }
        return source.append("\nbehavior f : (n: Int) -> Int\nlet f (n) = a")
                .append(links).append('\n').toString();
    }

    @Test
    void aLongChainOfValuesIsNoLargerToAnAnalysisForBeingLonger() {
        int shorter = nodes(analysed(chain(12), "f"));
        int longer = nodes(analysed(chain(20), "f"));

        assertTrue(longer <= shorter,
                "a chain that is longer is read as one that is: past the depth a copy is worth, a "
                        + "value is one reference (" + shorter + " and " + longer + ")");
    }
}
