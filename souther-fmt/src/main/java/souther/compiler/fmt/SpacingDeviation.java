package souther.compiler.fmt;

import souther.compiler.cst.SyntaxElement;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.cst.SyntaxNode;
import souther.compiler.cst.SyntaxToken;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Where a source writes something else between two tokens than the canonical form would, and which
 * rule says so.
 *
 * <p>A gate that says a file is not formatted has said what is wrong with it; naming the rule says
 * why. That was expensive while the answer lived in whichever literal a construct happened to
 * spell, because attributing a difference meant finding that literal. It is one call now: the rule
 * reads the two token kinds and the construct joining them, and all three are in the source's own
 * tree, so a deviation is the answer disagreeing with what is written and the rule it names is the
 * row that answered.
 *
 * <p>Only what two tokens on one line have between them. A source that broke a line where the
 * canonical form would not, or did not where it would, has departed from the rules about breaking
 * and this has nothing to say about it.
 *
 * <p>The construct is read from the source's tree. Where the canonical form rewrites what it read —
 * {@code let f = (x) -> x} is written {@code let f (x) = x} — the name here is the one the source
 * had and the canonical form's is the other; both answer the same, and if that ever stops being
 * true this is the place that has to ask the canonical form instead.
 */
public final class SpacingDeviation {

    /**
     * One place a source disagrees with the rule: where it is, the rule that answered — the
     * construct and the kind on each side — and the two answers.
     */
    public record Deviation(int offset, SyntaxKind joining, SyntaxKind left, SyntaxKind right,
            String written, String canonical) {

        /** The rule this deviates from, as its row is written. */
        public String rule() {
            return left + " " + right + " under " + joining;
        }
    }

    private SpacingDeviation() {
    }

    /** Every place {@code file} writes something between two tokens of a line that the rule does
     * not. {@code source} is the text {@code file} was parsed from. */
    public static List<Deviation> of(SyntaxNode file, String source) {
        List<SyntaxToken> code = new ArrayList<>();
        gather(file, code);
        code.removeIf(t -> t.isTrivia() || t.kind() == SyntaxKind.EOF);
        List<Deviation> out = new ArrayList<>();
        for (int i = 0; i + 1 < code.size(); i++) {
            SyntaxToken left = code.get(i);
            SyntaxToken right = code.get(i + 1);
            String gap = source.substring(left.end(), right.start());
            if (gap.indexOf('\n') >= 0) {
                continue;   // the break rules', not this one's
            }
            SyntaxNode joining = joining(left, right);
            String canonical;
            try {
                canonical = Spacing.between(joining.kind(), left.kind(), right.kind());
            } catch (IllegalStateException _) {
                // An adjacency the rule holds no row for. It is a gap in the rule rather than a
                // fault in the source, and a gate is the wrong place to raise it.
                continue;
            }
            if (!gap.equals(canonical)) {
                out.add(new Deviation(left.end(), joining.kind(), left.kind(), right.kind(),
                        gap, canonical));
            }
        }
        return out;
    }

    /** The construct that joins two tokens: the deepest node holding both. */
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
        throw new IllegalStateException("two tokens of one file with no node holding both");
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
}
