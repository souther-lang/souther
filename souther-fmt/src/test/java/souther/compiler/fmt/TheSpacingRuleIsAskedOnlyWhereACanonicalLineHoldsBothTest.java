package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import souther.compiler.cst.CstParser;
import souther.compiler.cst.SyntaxElement;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.cst.SyntaxNode;
import souther.compiler.cst.SyntaxToken;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every adjacency a source can write on one line is one the spacing rule holds, and the ones it has
 * no answer for are the ones the canonical form never writes on a line at all.
 *
 * <p>{@link TheRuleAnswersEveryBoundaryTheGrammarCanBuildTest} takes its candidates from the
 * boundaries the formatter writes, which is the path being validated: a boundary the canonical form
 * always breaks is one the formatter never asks the rule about, so no row was ever needed and none
 * is missed. A witness asks the other question — a source wrote these two tokens on one line, is
 * that what the canonical form writes? — and the adjacencies a source can write are a strictly
 * larger set.
 *
 * <p>So the candidates here come from the parser: a source it accepts is a source whose adjacencies
 * the language admits, and they are read off the source's own tokens rather than off the document
 * the formatter built from them.
 *
 * <p>What the rule owes them is not an answer everywhere. Where the canonical form always breaks an
 * adjacency there is no spacing it writes, and a rule made total over those would be inventing one.
 * What it owes is that every such hole is explained by that and not by a missing row — the domain is
 * total and the expectation is partial, with the break decision above it saying where.
 */
class TheSpacingRuleIsAskedOnlyWhereACanonicalLineHoldsBothTest {

    /** The spacing rule's unit: two token kinds and the construct that joins them. */
    private record Adjacency(SyntaxKind joining, SyntaxKind left, SyntaxKind right)
            implements Comparable<Adjacency> {

        @Override
        public String toString() {
            return left + " " + right + " under " + joining;
        }

        @Override
        public int compareTo(Adjacency other) {
            return toString().compareTo(other.toString());
        }
    }

    /**
     * Every adjacency a source the parser accepts writes on one line.
     *
     * <p>Two sources per corpus entry and then some: the entry itself, and one for each break the
     * canonical form writes whatever the width, with that break closed up into a space. The second
     * is where the boundaries the formatter never asks the rule about come from — closing one up
     * gives a source that has those two tokens on a line, and the parser says whether the language
     * admits it. A candidate the parser refuses is not one.
     *
     * <p>The joining construct is the deepest source node holding both tokens. Over these sources
     * that is the construct the canonical form names too — the two structures differ only where a
     * definition's lambda is lifted — so a hole found here is a hole in the rule and not a
     * disagreement about which construct is being asked.
     */
    private static Set<Adjacency> candidates;

    /** The sweep's answer, taken once: both checks below read all of it, and the corpus does not
     *  change while the class runs. */
    private static Set<Adjacency> admitted() {
        if (candidates == null) {
            candidates = sweep();
        }
        return candidates;
    }

    private static Set<Adjacency> sweep() {
        Set<Adjacency> out = new TreeSet<>();
        for (String source : WhatGoesBetweenTwoTokensOnALineTest.corpus()) {
            out.addAll(onOneLine(source));
            for (String closed : linesClosedUp(source)) {
                out.addAll(onOneLine(closed));
            }
        }
        return out;
    }

    /** Every adjacency {@code source} writes on one line, or nothing where the parser refuses it. */
    private static Set<Adjacency> onOneLine(String source) {
        CstParser.Result parsed = CstParser.parse(source);
        if (!parsed.errors().isEmpty()) {
            return Set.of();
        }
        Set<Adjacency> out = new TreeSet<>();
        List<SyntaxToken> code = code(parsed.root());
        for (int i = 0; i + 1 < code.size(); i++) {
            SyntaxToken left = code.get(i);
            SyntaxToken right = code.get(i + 1);
            if (source.substring(left.end(), right.start()).indexOf('\n') >= 0) {
                continue;   // the source did not write these two on one line
            }
            SyntaxKind joining = deepestHolding(left, right);
            if (joining != null) {
                out.add(new Adjacency(joining, left.kind(), right.kind()));
            }
        }
        return out;
    }

    /** The canonical form of {@code source} with one of its forced breaks written as a space, one
     *  variant per break. What the parser makes of each is the variant's own business. */
    private static List<String> linesClosedUp(String source) {
        Layout layout = Formatter.canonicalize(CstParser.parse(source).root()).layout();
        String text = layout.text();
        List<String> out = new ArrayList<>();
        for (Newline n : layout.breaks()) {
            if (!(n.cause() instanceof Newline.Cause.Forced)) {
                continue;   // one the width settled: the formatter already asks the rule about it
            }
            int after = n.offset() + 1 + n.indent();
            if (after > text.length()) {
                continue;
            }
            out.add(text.substring(0, n.offset()) + " " + text.substring(after));
        }
        return out;
    }

    /** Where the canonical form writes each adjacency, as the policies of the boundaries it has
     *  there. An adjacency with no boundary of its own is one the canonical form does not write. */
    private static Map<Adjacency, Set<TokenDoc.Break>> policies;

    private static Map<Adjacency, Set<TokenDoc.Break>> canonicalPolicies() {
        if (policies == null) {
            policies = readOffTheCanonicalForm();
        }
        return policies;
    }

    /** The corpus canonicalised the once, which is what the two checks are both asking of it. */
    private static Map<Adjacency, Set<TokenDoc.Break>> readOffTheCanonicalForm() {
        Map<Adjacency, Set<TokenDoc.Break>> out = new LinkedHashMap<>();
        for (String source : WhatGoesBetweenTwoTokensOnALineTest.corpus()) {
            for (Gaps.Boundary b : Gaps.boundaries(
                    Formatter.canonicalize(CstParser.parse(source).root()).construction().doc())) {
                if (b.joining() == null) {
                    continue;   // a comment stands beside it, and no construct joins the two
                }
                out.computeIfAbsent(new Adjacency(b.joining(), b.left(), b.right()),
                        _ -> new TreeSet<>()).add(b.policy());
            }
        }
        return out;
    }

    /**
     * The rule answers every adjacency a source writes on a line, except where the canonical form
     * writes that adjacency only as a break.
     */
    @Test
    void everyAdjacencyASourceWritesIsAnsweredOrIsNeverOnALine() {
        Map<Adjacency, Set<TokenDoc.Break>> canonical = canonicalPolicies();
        Set<Adjacency> unanswered = new TreeSet<>();
        Set<Adjacency> inapplicable = new TreeSet<>();
        int answered = 0;
        for (Adjacency unit : admitted()) {
            try {
                Spacing.between(unit.joining(), unit.left(), unit.right());
                answered++;
                continue;
            } catch (IllegalStateException _) {
                // no row: allowed only where the canonical form never writes this one inline
            }
            Set<TokenDoc.Break> policies = canonical.get(unit);
            if (policies != null && policies.equals(Set.of(TokenDoc.Break.ALWAYS))) {
                inapplicable.add(unit);
            } else {
                unanswered.add(unit);
            }
        }

        assertEquals(new TreeSet<Adjacency>(), unanswered,
                "adjacencies a source writes on one line that the rule has no answer for, and that"
                        + " the canonical form does not always break either");
        assertTrue(answered > 200,
                "only " + answered + " adjacencies were answered; the candidates are not being"
                        + " reached");
        assertTrue(!inapplicable.isEmpty(),
                "no adjacency was found inapplicable, so the branch that explains a hole by the"
                        + " break above it never ran and this test would pass with it removed");
        assertTrue(inapplicable.contains(
                        new Adjacency(SyntaxKind.DATA_DEF, SyntaxKind.IDENT,
                                SyntaxKind.INVARIANT_KW)),
                "a source can write `data P = Int invariant ...` on one line and the canonical form"
                        + " never does, which is the adjacency this check was written for: "
                        + inapplicable);
    }

    /**
     * And an adjacency the rule does not answer is one the canonical form breaks at every boundary
     * it has for it — the partiality is the break decision's and not a gap in the rows.
     *
     * <p>Written out because the set is small and each of them is a claim: these are adjacencies a
     * reader can write and the formatter will not keep on a line, so a witness for one of them
     * answers with the break rule rather than with a space.
     */
    @Test
    void andTheOnesItDoesNotAnswerAreBrokenWhereverTheCanonicalFormWritesThem() {
        Map<Adjacency, Set<TokenDoc.Break>> canonical = canonicalPolicies();
        Map<String, Set<TokenDoc.Break>> holes = new TreeMap<>();
        for (Adjacency unit : admitted()) {
            try {
                Spacing.between(unit.joining(), unit.left(), unit.right());
            } catch (IllegalStateException _) {
                holes.put(unit.toString(), canonical.get(unit));
            }
        }
        for (Map.Entry<String, Set<TokenDoc.Break>> e : holes.entrySet()) {
            assertEquals(Set.of(TokenDoc.Break.ALWAYS), e.getValue(),
                    e.getKey() + " has no row and is not one the canonical form always breaks");
        }
    }

    /** The deepest node holding both tokens, which is the construct that joins them. */
    private static SyntaxKind deepestHolding(SyntaxToken left, SyntaxToken right) {
        List<SyntaxNode> above = ancestors(right);
        for (SyntaxNode n : ancestors(left)) {
            if (above.contains(n)) {
                return n.kind();
            }
        }
        return null;
    }

    /** The nodes a token is under, innermost first. */
    private static List<SyntaxNode> ancestors(SyntaxToken token) {
        List<SyntaxNode> out = new ArrayList<>();
        for (SyntaxNode n = token.parent(); n != null; n = n.parent()) {
            out.add(n);
        }
        return out;
    }

    /** The file's tokens, comments and whitespace left out. */
    private static List<SyntaxToken> code(SyntaxNode node) {
        List<SyntaxToken> out = new ArrayList<>();
        collect(node, out);
        return out;
    }

    private static void collect(SyntaxNode node, List<SyntaxToken> out) {
        for (SyntaxElement e : node.children()) {
            switch (e) {
                case SyntaxNode n -> collect(n, out);
                case SyntaxToken t -> {
                    // The end of the file is not a token the canonical form writes, so there is no
                    // boundary in front of it and no spacing to ask about.
                    if (!t.isTrivia() && t.kind() != SyntaxKind.LINE_COMMENT
                            && t.kind() != SyntaxKind.EOF) {
                        out.add(t);
                    }
                }
            }
        }
    }
}
