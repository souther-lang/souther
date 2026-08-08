package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxElement;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.cst.SyntaxNode;
import souther.compiler.cst.SyntaxToken;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the document says joins two tokens is what the canonical form says joins them: the deepest
 * node holding both, in the tree the output parses back to.
 *
 * <p>Nothing else catches this. The rule's answer can be right while the name it was asked under is
 * wrong, because two constructs can answer the same — and where the formatter rewrites what it read
 * they routinely do. A definition written {@code let f = (x) -> x} is written back as
 * {@code let f (x) = x}, so its brackets come from a lambda and are a parameter list in the output,
 * and both of those say {@code ""} today. A check on what was written sees nothing; a check on the
 * table sees nothing; this is what says the two names have to be the same one.
 *
 * <p>It is what the deviation witness of issue #444 needs. A witness names the rule it broke, and
 * the rule's name is the construct together with the two kinds — so the construct has to be one its
 * reader can find in the canonical form rather than one only the formatter knows.
 */
class TheConstructABoundaryNamesIsTheOneTheOutputHasTest {

    /** Every code token of a source, in the order it is written. */
    private static List<SyntaxToken> written(String source) {
        List<SyntaxToken> out = new ArrayList<>();
        gather(CstParser.parse(source).root(), out);
        return out.stream().filter(t -> !t.isTrivia() && t.kind() != SyntaxKind.EOF).toList();
    }

    private static void gather(SyntaxNode n, List<SyntaxToken> out) {
        for (SyntaxElement e : n.children()) {
            if (e instanceof SyntaxNode c) {
                gather(c, out);
            } else if (e instanceof SyntaxToken t) {
                out.add(t);
            }
        }
    }

    /** The construct that joins two tokens of the canonical form: the deepest node holding both. */
    private static SyntaxNode joining(SyntaxToken left, SyntaxToken right) {
        Set<SyntaxNode> above = new LinkedHashSet<>();
        for (SyntaxNode p = left.parent(); p != null; p = p.parent()) {
            above.add(p);
        }
        for (SyntaxNode p = right.parent(); p != null; p = p.parent()) {
            if (above.contains(p)) {
                return p;
            }
        }
        throw new AssertionError("two tokens of one file with no node holding both");
    }

    /** The boundaries of a document, less the newline a file ends with, which joins nothing. */
    private static List<Gaps.Boundary> boundaries(TokenDoc doc) {
        return Gaps.boundaries(doc).stream()
                .filter(b -> b.left() != null && b.right() != null).toList();
    }

    @Test
    void eachOfThemNamesWhatTheCanonicalFormHasThere() {
        List<String> wrong = new ArrayList<>();
        int compared = 0;
        for (String source : WhatGoesBetweenTwoTokensOnALineTest.corpus()) {
            List<Gaps.Boundary> said = boundaries(Formatter.document(CstParser.parse(source).root()));
            List<SyntaxToken> output = written(Formatter.format(source));
            assertEquals(output.size() - 1, said.size(),
                    "one boundary for each adjacency of the canonical form of:\n" + source);
            for (int i = 0; i < said.size(); i++) {
                Gaps.Boundary b = said.get(i);
                SyntaxToken left = output.get(i);
                SyntaxToken right = output.get(i + 1);
                assertEquals(left.kind() + " " + right.kind(), b.left() + " " + b.right(),
                        "boundary " + i + " stands between other tokens than the output's");
                if (b.joining() == null) {
                    continue;   // a comment stands in it, so no construct was asked
                }
                compared++;
                SyntaxKind has = joining(left, right).kind();
                if (b.joining() != has) {
                    wrong.add(left.kind() + " " + right.kind() + ": the document says "
                            + b.joining() + " and the canonical form says " + has);
                }
            }
        }
        assertEquals(List.of(), wrong.stream().distinct().toList());
        assertTrue(compared > 1000, "only " + compared + " boundaries were compared");
    }
}
