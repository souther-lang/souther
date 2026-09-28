package souther.compiler.core;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;
import souther.compiler.ast.DefinitionName;
import souther.compiler.ast.Hir;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a body holds is what its author wrote, and not what its references multiply out to.
 *
 * <p>A value denotes as if its body stood at each reference (ADR-0072), and a compiler that
 * realises that by copying makes a body of a size the source cannot be read for: a value named
 * twice is written twice, and a chain of values that each name the one before them twice is a tree
 * that doubles with every further binding while the source grows by a line.
 *
 * <p>Held as a count and not as a time. What the sharing is for is the size of what every walk
 * below has to descend, and that is a property of the tree — a wall clock measures the machine the
 * run was on as much as it measures this, and says nothing on the run where the machine was quick.
 *
 * <p>Two chains of one length, differing in one thing: whether each binding reads the one before it
 * once or twice. The second holds what the first holds and a few nodes more — an operand where
 * there was a literal — so a reading that copies is a reading this tells apart at once.
 */
class AValueNamedTwiceIsBuiltOnceTest {

    /** Long enough that copying is out of reach — a copying build of this chain holds more nodes
     *  than a run has room for — and short enough that a shared one is ordinary. */
    private static final int LINKS = 24;

    /** What reading a value twice may add over reading it once, per link. The two chains write the
     *  same operator over the same number of operands, so what differs is a literal against a name
     *  and whatever one binding's own shape costs. */
    private static final int PER_LINK = 8;

    private static String chain(int links, boolean twice) {
        StringBuilder source = new StringBuilder("module m exposing (f)\n\nlet a0 = 1m\n");
        for (int i = 1; i <= links; i++) {
            source.append("let a").append(i).append(" = a").append(i - 1)
                    .append(twice ? " * a" + (i - 1) : " * 1m").append('\n');
        }
        return source.append("\nbehavior f : (x: Int) -> Decimal\nlet f (x) = a")
                .append(links).append('\n').toString();
    }

    /** How many nodes the body the backend emits from holds. */
    private static int nodesIn(int links, boolean twice) {
        Compilation compiled = Compiler.compiled(chain(links, twice), "m");
        Hir.Expr body = compiled.db()
                .ask(new Bodies.LoweredBody("m", new DefinitionName("f")))
                .value().value().definition().writtenBody();
        return count(body);
    }

    private static int count(Hir.Expr e) {
        if (e == null) {
            return 0;
        }
        int[] held = {1};
        Hir.forEachChild(e, child -> held[0] += count(child));
        return held[0];
    }

    @Test
    void aChainOfValuesEachNamedTwiceIsNoLargerThanTheSameChainNamedOnce() {
        int once = nodesIn(LINKS, false);
        int twice = nodesIn(LINKS, true);
        assertTrue(twice <= once + LINKS * PER_LINK,
                "a chain whose links are each named twice was built from " + twice
                        + " nodes where the same chain named once was built from " + once
                        + ": a value named twice is being written twice");
    }

    /**
     * And the count rises with the chain rather than with what it multiplies out to.
     *
     * <p>Beside the comparison above because the two say different things. That one holds this
     * build to what the one-reference build costs; this one holds it to its own shape at another
     * length, which is what says the relation is the chain's length and not a constant that
     * happened to fit.
     */
    @Test
    void twiceTheChainIsAboutTwiceTheBody() {
        int shorter = nodesIn(LINKS, true);
        int longer = nodesIn(LINKS * 2, true);
        assertTrue(longer <= shorter * 3,
                "a chain of " + (LINKS * 2) + " links was built from " + longer
                        + " nodes where one of " + LINKS + " was built from " + shorter
                        + ": what the body holds is not the length of the chain");
    }
}
