package souther.compiler.check;

import souther.compiler.Compiler;

import org.junit.jupiter.api.Test;
import souther.test.Growth;

import java.util.LinkedHashMap;
import java.util.SequencedMap;
import java.util.function.IntFunction;

/**
 * A chain of names, each the one before it with text added, is named a link at a time.
 *
 * <p>A text is filed under the text it comes to, and a name under what it was entered as. So a
 * link's text is the text of the name before it joined to what it adds, and nothing follows the
 * chain back to its head — which naming each link by folding everything under it did, once per link,
 * for the square of the chain's length.
 *
 * <p>Held as how three counts grow as the chain doubles, through the whole compiler, since that is
 * where a link is named once by the walk entering it and again by every reader asking about it. The
 * names the fold follows, the walks the reading starts, and the nodes those walks name: the last is
 * what a fold moved into the walk would show, where the first would show nothing. Asked of a chain
 * whose head is an input and of one whose head is written, since only the second has a text at every
 * link. The longest chain is what a block holds: each link is two levels of structure, and a
 * definition holds 320.
 */
class AChainOfJoinedTextsIsNamedALinkAtATimeTest {

    private static final int[] LINKS = {18, 36, 72, 144};

    private static final String HEAD = """
            module demo
            data Code = String
                invariant jp = String.startsWith("JP", value)
            behavior f : (x: String, s: String) -> Code
                constructs Code
            """;

    /** {@code links} names each joining text to the one before it, the first given {@code head},
     *  and a guard on the last. */
    private static String chain(int links, String head) {
        StringBuilder body = new StringBuilder("let f (x, s) = {\n    let a0 = " + head + "\n");
        for (int i = 1; i <= links; i++) {
            body.append("    let a").append(i).append(" = a").append(i - 1).append(" ++ \"P\"\n");
        }
        body.append("    if String.startsWith(a").append(links)
                .append(", s) then Code(s) else Code(\"JP\")\n}\n");
        return HEAD + body;
    }

    private record Counts(long folded, long walks, long named) {}

    private static Counts countedOver(String module) {
        long[] folded = {0};
        long[] walks = {0};
        long[] named = {0};
        FoldedValue.FOLDED = folded;
        Terms.COUNTING_WALKS = walks;
        Terms.COUNTING_NAMED = named;
        try {
            Compiler.compileWithWarnings(module);
        } finally {
            FoldedValue.FOLDED = null;
            Terms.COUNTING_WALKS = null;
            Terms.COUNTING_NAMED = null;
        }
        return new Counts(folded[0], walks[0], named[0]);
    }

    private static void doublingTheChainAboutDoublesEachCount(IntFunction<String> module) {
        SequencedMap<Integer, Long> folded = new LinkedHashMap<>();
        SequencedMap<Integer, Long> walks = new LinkedHashMap<>();
        SequencedMap<Integer, Long> named = new LinkedHashMap<>();
        for (int links : LINKS) {
            Counts counts = countedOver(module.apply(links));
            folded.put(links, counts.folded());
            walks.put(links, counts.walks());
            named.put(links, counts.named());
        }
        Growth.eachAtMost(folded, 3, 1);
        Growth.eachAtMost(walks, 3, 1);
        Growth.eachAtMost(named, 3, 1);
    }

    @Test
    void aChainWhoseHeadIsWritten() {
        doublingTheChainAboutDoublesEachCount(links -> chain(links, "\"J\""));
    }

    @Test
    void aChainWhoseHeadIsAnInput() {
        doublingTheChainAboutDoublesEachCount(links -> chain(links, "x"));
    }
}
