package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule may name a position deeper than the reading of an input walks to, and that is not an error.
 *
 * <p>The walk stops at two levels, where a report stops being about anything an author would call
 * one input. Nothing stops a rule from naming what is under that: the reader that turns an
 * expression into a path follows as many fields as are written. So a term at a path the reading has
 * no position for is an ordinary thing to be handed, and the reading already has a word for it —
 * {@code the walk stopped before reaching what is under it} — which is what a report says of the
 * position above it.
 *
 * <p>Told apart from a term of some other behavior's input, which is a caller's mistake and is
 * refused as one. Both are "no position of this input is at that path", and only one of them is
 * anybody's fault: a path under a parameter of this input belongs to it however far down it goes,
 * and what is unknown there is what the rules relate it to rather than whose it is.
 */
class ATermMayNameAPositionTheWalkStoppedShortOfTest {

    /** Two fields three levels down, compared against each other. The line is between two positions
     *  the walk never reached. */
    private static final String DEEPER_THAN_THE_WALK = """
            module example.deep

            data Inner = { a: Int, b: Int }
            data Mid   = { inner: Inner }
            data Outer = { mid: Mid }

            data No = { why: Int }
            data Yes = { v: Int }
            data Result = No | Yes

            behavior f : (o: Outer) -> Result
                constructs Yes, No
            let f (o) = {
                guard o.mid.inner.a < o.mid.inner.b else No { why = 0 }
                Yes { v = 1 }
            }

            example f
                | "under" : (Outer { mid = Mid { inner = Inner { a = 1, b = 2 } } }) -> Yes { v = 1 }
            """;

    @Test
    void aLineBetweenTwoPositionsBelowTheWalkIsStillMeasured() {
        String report = report(DEEPER_THAN_THE_WALK);

        assertTrue(report.contains("the walk stopped before reaching what is under it"), report);
        assertTrue(report.contains("f/o.mid.inner.a = o.mid.inner.b"), report);
    }

    /** The same two fields, held one apart, which is a rule no operand of the comparison names. */
    private static final String REWRITTEN_BY_THE_ARITHMETIC = DEEPER_THAN_THE_WALK
            .replace("o.mid.inner.a < o.mid.inner.b", "o.mid.inner.a + 1 < o.mid.inner.b");

    /**
     * And so is one the arithmetic had to rewrite to find the two positions in.
     *
     * <p>Which is the case that has nowhere else to get the answer. A comparison written between the
     * two positions themselves names each of them with an operand, and something of the position can
     * be had from what the checker gave that operand; {@code a + 1 < b} names neither, so the order
     * each position is counted on is the reading of the declarations' to say or nobody's.
     *
     * <p>That reading stops at {@link souther.compiler.inputs.InputDomain#MAX_DEPTH} and the
     * declarations do not, so it follows the type the rest of the way down. Made to stop where the
     * positions stop — a null for a path with no position, which reads like tidying up — this line
     * is not drawn at all.
     */
    @Test
    void soIsALineTheArithmeticHadToRewriteToFind() {
        String report = report(REWRITTEN_BY_THE_ARITHMETIC);

        // The line is where `a` is one below `b`, so the point on it is the pair two apart: the
        // rule is written `<` and the last pair satisfying it is the one before they are one apart.
        assertTrue(report.contains("f/o.mid.inner.a = o.mid.inner.b - 2"), report);
    }

    private static String report(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        return AdequacyReport.of(compilation).human(SourceNameResolver.identity());
    }
}
