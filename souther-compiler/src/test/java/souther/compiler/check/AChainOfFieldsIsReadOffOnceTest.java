package souther.compiler.check;

import souther.compiler.Compiler;

import org.junit.jupiter.api.Test;
import souther.test.Growth;

import java.util.LinkedHashMap;
import java.util.SequencedMap;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A chain of fields is read off what it is read off once, however deep it goes.
 *
 * <p>A field read off a construction is what the construction gave it, which means walking the
 * names of the chain against the construction. Off anything else — an input, a place, a value
 * nothing built here — there is nothing to walk them against, and the chain is the one the interner
 * extends from the path a projection already has worked out. Writing the names out there anyway is
 * work per name per chain, the square of the depth over a chain whose every prefix is read, and no
 * count of walks or of named nodes sees it, since it happens inside naming one node.
 *
 * <p>So three counts as the chain doubles: the names written out against a construction, the walks
 * the reading starts, and the nodes those walks name. The first is none off an input, and grows
 * with the chain off records built where they are read.
 */
class AChainOfFieldsIsReadOffOnceTest {

    private static final int[] DEPTHS = {8, 16, 32};

    /** {@code R0} holding a text, and each {@code Rk} holding the one below it. */
    private static String records(int depth) {
        StringBuilder out = new StringBuilder("""
                module demo
                data Code = String
                    invariant jp = String.startsWith("JP", value)
                data R0 = { p: String }
                """);
        for (int k = 1; k <= depth; k++) {
            out.append("data R").append(k).append(" = { a: R").append(k - 1).append(" }\n");
        }
        return out.toString();
    }

    /** {@code root} read down to the text: {@code root.a.a ... .a.p}. */
    private static String downTo(String root, int depth) {
        return root + ".a".repeat(depth) + ".p";
    }

    private static String offAnInput(int depth) {
        return records(depth) + """
                behavior f : (r: RTOP, s: String) -> Code
                    constructs Code
                let f (r, s) = if String.startsWith(TEXT, s) then Code(s) else Code("JP")
                """.replace("RTOP", "R" + depth).replace("TEXT", downTo("r", depth));
    }

    private static String offRecordsBuiltHere(int depth) {
        StringBuilder constructs = new StringBuilder("Code");
        StringBuilder body = new StringBuilder("    let v0 = R0 { p = \"JP\" }\n");
        for (int k = 0; k <= depth; k++) {
            constructs.append(", R").append(k);
            if (k > 0) {
                body.append("    let v").append(k).append(" = R").append(k)
                        .append(" { a = v").append(k - 1).append(" }\n");
            }
        }
        return records(depth) + "behavior f : (s: String) -> Code\n    constructs " + constructs
                + "\nlet f (s) = {\n" + body + "    if String.startsWith("
                + downTo("v" + depth, depth) + ", s) then Code(s) else Code(\"JP\")\n}\n";
    }

    private record Counts(long readOff, long walks, long named) {}

    private static Counts countedOver(String module) {
        long[] readOff = {0};
        long[] walks = {0};
        long[] named = {0};
        Terms.COUNTING_READ_OFF = readOff;
        Terms.COUNTING_WALKS = walks;
        Terms.COUNTING_NAMED = named;
        try {
            Compiler.compileWithWarnings(module);
        } finally {
            Terms.COUNTING_READ_OFF = null;
            Terms.COUNTING_WALKS = null;
            Terms.COUNTING_NAMED = null;
        }
        return new Counts(readOff[0], walks[0], named[0]);
    }

    @Test
    void offAnInputNoNameIsWrittenOut() {
        SequencedMap<Integer, Long> walks = new LinkedHashMap<>();
        SequencedMap<Integer, Long> named = new LinkedHashMap<>();
        for (int depth : DEPTHS) {
            Counts counts = countedOver(offAnInput(depth));
            assertEquals(0, counts.readOff(), "a chain read off an input, " + depth + " deep");
            walks.put(depth, counts.walks());
            named.put(depth, counts.named());
        }
        Growth.eachAtMost(walks, 3, 1);
        Growth.eachAtMost(named, 3, 1);
    }

    @Test
    void offRecordsBuiltHereTheNamesGrowWithTheChain() {
        SequencedMap<Integer, Long> readOff = new LinkedHashMap<>();
        SequencedMap<Integer, Long> walks = new LinkedHashMap<>();
        SequencedMap<Integer, Long> named = new LinkedHashMap<>();
        for (int depth : DEPTHS) {
            Counts counts = countedOver(offRecordsBuiltHere(depth));
            readOff.put(depth, counts.readOff());
            walks.put(depth, counts.walks());
            named.put(depth, counts.named());
        }
        Growth.eachAtMost(readOff, 3, 1);
        Growth.eachAtMost(walks, 3, 1);
        Growth.eachAtMost(named, 3, 1);
    }

    /** And what the chain comes to is the text written at its foot. */
    @Test
    void offRecordsBuiltHereTheTextAtTheFootDischargesTheRule() {
        assertEquals(java.util.List.of(), Compiler.compileWithWarnings(offRecordsBuiltHere(8))
                .warnings().stream().map(d -> d.code()).toList());
    }
}
