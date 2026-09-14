package souther.compiler.fmt;

import org.junit.jupiter.api.Tag;
import org.junit.jupiter.api.Test;

import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxToken;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The table an offset is answered from says what walking the tokens said.
 *
 * <p>The families ask two questions of a run of code tokens — which adjacency an offset stands in,
 * and which token stands in front of it — and both used to be answered by walking the run from its
 * first token. The walk is what the rules were written against, so the table that replaced it is
 * held against the walk rather than against a second statement of what the answers ought to be.
 *
 * <p>Asked at every offset of every source in the corpus, and not at the offsets the families
 * happen to ask about. Which of them a family asks is that family's to change, and a table that
 * agreed only where it is asked today would be one the next question can find a hole in.
 */
@Tag("population")
class WhereAnOffsetStandsAmongTheTokensIsWhatWalkingThemSaysTest {

    /** Which adjacency {@code at} stands in, by walking: the first one it is inside. */
    private static int walkToTheAdjacency(List<SyntaxToken> tokens, int at) {
        for (int i = 0; i + 1 < tokens.size(); i++) {
            if (tokens.get(i).end() <= at && at <= tokens.get(i + 1).start()) {
                return i;
            }
        }
        return -1;
    }

    /** Which token stands in front of {@code at}, by walking: the last one to have ended. */
    private static int walkToTheTokenInFront(List<SyntaxToken> tokens, int at) {
        int found = -1;
        for (int i = 0; i < tokens.size(); i++) {
            if (tokens.get(i).end() <= at) {
                found = i;
            }
        }
        return found;
    }

    /** Every offset of a text, and a few on either side of it. */
    private static void heldAtEveryOffset(String text, List<SyntaxToken> tokens, String said) {
        Witnesses.Run run = new Witnesses.Run(tokens);
        for (int at = -2; at <= text.length() + 2; at++) {
            assertEquals(walkToTheAdjacency(tokens, at), run.adjacencyAt(at),
                    "the adjacency at offset " + at + " of " + said);
            assertEquals(walkToTheTokenInFront(tokens, at), run.inFrontOf(at),
                    "the token in front of offset " + at + " of " + said);
        }
    }

    @Test
    void theTableSaysWhatTheWalkSaidOverTheCorpus() {
        for (String source : WhatGoesBetweenTwoTokensOnALineTest.corpus()) {
            String canonical = Formatter.format(CstParser.parse(source).root());
            heldAtEveryOffset(source, Witnesses.code(CstParser.parse(source).root()),
                    "a source of the corpus");
            heldAtEveryOffset(canonical, Witnesses.code(CstParser.parse(canonical).root()),
                    "the canonical form of a source of the corpus");
        }
    }

    /**
     * And a run with nothing in it, or one token, which the corpus has neither of.
     *
     * <p>Both are runs with no adjacency at all, and the second still has a token that can stand in
     * front of an offset. A table sized from the last token is where those two part company.
     */
    @Test
    void andOverARunTheCorpusDoesNotHave() {
        heldAtEveryOffset("", List.of(), "an empty run");

        String one = "module m exposing (a)\n";
        List<SyntaxToken> tokens = Witnesses.code(CstParser.parse(one).root());
        heldAtEveryOffset(one, tokens.subList(0, 1), "a run of one token");
        heldAtEveryOffset(one, tokens.subList(0, 2), "a run of two tokens");
    }

    /**
     * And a run is written in order, which is what lets either question be searched for.
     *
     * <p>The walk this replaced read the run from its first token and needed nothing of the sort. A
     * search does: it is right because a token that begins later ends later, and a run that broke
     * that would be answered wrongly at offsets no case above happens to ask about. So it is held
     * of the runs the corpus makes rather than assumed of the tree that makes them.
     */
    @Test
    void andARunIsWrittenInOrder() {
        for (String source : WhatGoesBetweenTwoTokensOnALineTest.corpus()) {
            String canonical = Formatter.format(CstParser.parse(source).root());
            for (String text : List.of(source, canonical)) {
                List<SyntaxToken> tokens = Witnesses.code(CstParser.parse(text).root());
                for (int i = 0; i + 1 < tokens.size(); i++) {
                    assertTrue(tokens.get(i).start() <= tokens.get(i + 1).start(),
                            "a token begins before the one written in front of it, at " + i);
                    assertTrue(tokens.get(i).end() <= tokens.get(i + 1).end(),
                            "a token ends before the one written in front of it, at " + i);
                    assertTrue(tokens.get(i).end() <= tokens.get(i + 1).start(),
                            "two tokens of a run overlap, at " + i);
                }
            }
        }
    }

    /**
     * And the sweep reaches the offsets the two questions are told apart by.
     *
     * <p>An offset inside a token stands in no adjacency and still has a token in front of it; one
     * past the last token has neither an adjacency nor a token after it; and where two tokens touch,
     * the adjacency between them is a single offset. Held over a corpus that had none of those, the
     * check above is a check of nothing.
     */
    @Test
    void andTheCorpusHasTheOffsetsThatTellTheTwoApart() {
        int inside = 0;
        int past = 0;
        int touching = 0;
        int spanning = 0;
        for (String source : WhatGoesBetweenTwoTokensOnALineTest.corpus()) {
            List<SyntaxToken> tokens = Witnesses.code(CstParser.parse(source).root());
            Witnesses.Run run = new Witnesses.Run(tokens);
            for (int i = 0; i + 1 < tokens.size(); i++) {
                if (tokens.get(i).end() == tokens.get(i + 1).start()) {
                    touching++;
                } else {
                    spanning++;
                }
            }
            for (int at = 0; at <= source.length(); at++) {
                if (run.adjacencyAt(at) < 0 && run.inFrontOf(at) >= 0
                        && run.inFrontOf(at) + 1 < tokens.size()) {
                    inside++;
                }
            }
            int last = tokens.isEmpty() ? 0 : tokens.get(tokens.size() - 1).end();
            for (int at = last; at <= source.length(); at++) {
                if (run.inFrontOf(at) == tokens.size() - 1) {
                    past++;
                }
            }
        }
        assertTrue(inside > 0, "no offset of the corpus stands inside a token");
        assertTrue(past > 0, "no offset of the corpus stands past the last token");
        assertTrue(touching > 0, "no two tokens of the corpus touch");
        assertTrue(spanning > 0, "no two tokens of the corpus have anything between them");
    }
}
