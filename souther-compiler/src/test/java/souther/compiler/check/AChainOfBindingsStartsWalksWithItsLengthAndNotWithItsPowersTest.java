package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.Compiler;

import java.util.concurrent.atomic.AtomicLong;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many times a chain of bindings is read to name it, which grows with the chain.
 *
 * <p>Naming a {@code let} reads its initializer to name it, and entering the binding reads that
 * same initializer twice over — once for which value it is and once for what the term grammar
 * calls it. Where the initializer holds a binding of its own, each of those three readings reaches
 * the inner one and can start the three again, which is three readings to the length of the chain.
 * The program this is asked of duplicates nothing: every name in it is read once, and the number of
 * bindings is the length of the chain.
 *
 * <p>Held as a count of the walks the reading started rather than as a time. What a reading answers
 * is the same either way, so wall-clock is the only thing the answer leaves behind — and a measure
 * that reads a machine's load as a change in this compiler goes red for what it is not about.
 */
class AChainOfBindingsStartsWalksWithItsLengthAndNotWithItsPowersTest {

    /** A chain where each binding is read once, so nothing in it is copied and the number of
     *  bindings is the length of the chain. The conditional is what keeps each initializer a shape
     *  with something under it rather than a name standing for the one before. */
    private static String chainOf(int length) {
        StringBuilder source = new StringBuilder("module m exposing (f)\n\n")
                .append("let a0 = List.length([1, 2, 3])\n");
        for (int i = 1; i <= length; i++) {
            source.append("let a").append(i)
                    .append(" = (if List.length([1]) > 0 then a").append(i - 1)
                    .append(" else 0) + 1\n");
        }
        return source.append("\nbehavior f : (n: Int) -> Int\nlet f (n) = a")
                .append(length).append("\n").toString();
    }

    /** How many canonical-key walks compiling a chain of {@code length} bindings starts. */
    private static long walksOver(int length) {
        AtomicLong counting = new AtomicLong();
        Terms.COUNTING_WALKS = counting;
        try {
            Compiler.compileWithWarnings(chainOf(length));
        } finally {
            Terms.COUNTING_WALKS = null;
        }
        return counting.get();
    }

    /**
     * Twice the bindings, and the reading starts about twice the walks.
     *
     * <p>Asked as a ratio between two lengths rather than as a number at one. What a chain of a
     * given length costs is the sum of what every reader of it spends and is no claim of this
     * class's; what doubling the chain does to that is, and it is the whole of what went wrong.
     */
    @Test
    void twiceTheBindingsIsAboutTwiceTheWalks() {
        long shorter = walksOver(6);
        long longer = walksOver(12);
        assertTrue(shorter > 0, "the count was taken over a reading that named nothing");
        assertTrue(longer <= shorter * 3,
                "naming twice the chain started " + longer + " walks against " + shorter);
    }
}
