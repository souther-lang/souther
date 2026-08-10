package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxNode;
import souther.compiler.cst.SyntaxToken;

import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The formatter counts the comments it took against the comments the tree holds, and a construct
 * that takes none of its own is a failure rather than a file that quietly comes back shorter.
 *
 * <p>Structure is what makes the count small enough to be worth taking: comments are found in one
 * pass and consumed in one place. It is not what makes it right. A construct added later that never
 * asks for its comments loses them exactly as an {@code invariant} clause did, and no arrangement of
 * the code prevents that — only the count does.
 */
class TheFormatterAccountsForEveryCommentTest {

    private static final String SOURCE = """
            module m
            // above the data
            data D =
                { a: Int   // after the field
                , b: Int
                }
            """;

    @Test
    void everyCommentInTheTreeIsAccountedFor() {
        SyntaxNode file = CstParser.parse(SOURCE).root();

        assertEquals(List.of(), Formatter.unconsumed(file, offsetsOfEveryComment(file)));
    }

    @Test
    void andOneLeftOutIsReported() {
        SyntaxNode file = CstParser.parse(SOURCE).root();
        Set<Integer> allButOne = new HashSet<>(offsetsOfEveryComment(file));
        int dropped = allButOne.stream().min(Integer::compare).orElseThrow();
        allButOne.remove(dropped);

        List<SyntaxToken> missing = Formatter.unconsumed(file, allButOne);

        assertEquals(1, missing.size(), "one comment was left out and one should be reported");
        assertEquals(dropped, missing.get(0).start());
    }

    /** And the check is wired in: a real format of the same source raises nothing. */
    @Test
    void formattingThisSourceAccountsForAllOfThem() {
        String formatted = Formatter.format(SOURCE);

        assertTrue(formatted.contains("// above the data"), formatted);
        assertTrue(formatted.contains("// after the field"), formatted);
    }

    private static Set<Integer> offsetsOfEveryComment(SyntaxNode file) {
        Set<Integer> out = new HashSet<>();
        for (SyntaxToken t : Formatter.unconsumed(file, Set.of())) {
            out.add(t.start());
        }
        assertEquals(2, out.size(), "the source is written with two comments");
        return out;
    }
}
