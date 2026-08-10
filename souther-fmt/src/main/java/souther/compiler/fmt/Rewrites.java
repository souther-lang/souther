package souther.compiler.fmt;

import souther.compiler.cst.SyntaxElement;
import souther.compiler.cst.SyntaxKind;
import souther.compiler.cst.SyntaxNode;
import souther.compiler.cst.SyntaxToken;

import java.util.ArrayList;
import java.util.List;

/**
 * Where a source's code tokens and its canonical form's differ, and what the canonical form writes
 * there.
 *
 * <p>These are decisions like any other, and they were the ones with no unit. The layout rules
 * answer about a boundary between two tokens; which tokens those are is settled before any of them
 * is asked, and a source that wrote others left every one of them with nothing to pair.
 *
 * <p>Three of them, and the sites are read from the source rather than from what the formatter did
 * on the way through. Two are optional tokens the grammar admits and the canonical form has one
 * answer for — a comma after a run's last member, which it never writes, and the bar in front of a
 * match's first arm, which it always does. The third is a definition written as a lambda, whose
 * parameters the canonical form writes to the left of the {@code =}.
 */
final class Rewrites {

    private Rewrites() {
    }

    /** Which of the three a site is. */
    enum Kind {

        /** A comma after the last member of a comma-separated run, which is not written. */
        A_TRAILING_COMMA,

        /** The bar in front of a match's first arm, which is written. */
        THE_FIRST_ARMS_BAR,

        /** A definition whose body is a lambda, whose parameters are written to the left. */
        A_DEFINITIONS_PARAMETERS;

        /** What the rule says, for a reader who is being told their source does not. */
        String said() {
            return switch (this) {
                case A_TRAILING_COMMA ->
                        "a comma-separated run is written without a comma after its last member";
                case THE_FIRST_ARMS_BAR -> "a match writes every arm with its bar";
                case A_DEFINITIONS_PARAMETERS ->
                        "a definition writes its parameters to the left of the `=`";
            };
        }
    }

    /**
     * One site, the stretch of the source it is about, and the two answers.
     *
     * <p>{@code from} and {@code to} are what a repair writes over, which for an optional token the
     * source did not write is the empty stretch where it would stand.
     */
    record Site(Kind kind, int from, int to, String canonical, String source) {}

    /** Every site of {@code root} where the canonical form's tokens are not the source's. */
    static List<Site> sitesOf(SyntaxNode root) {
        List<Site> out = new ArrayList<>();
        walk(root, out);
        return out;
    }

    private static void walk(SyntaxNode node, List<Site> out) {
        trailingComma(node).ifPresent(comma -> out.add(new Site(Kind.A_TRAILING_COMMA,
                comma.start(), comma.end(), "", comma.text())));
        if (node.kind() == SyntaxKind.MATCH_EXPR) {
            // In front of what the arm writes and not in front of the arm: a node begins where its
            // leading trivia does, and a bar written there would stand at the end of the line above.
            firstArmWithoutItsBar(node).ifPresent(arm -> out.add(new Site(Kind.THE_FIRST_ARMS_BAR,
                    firstToken(arm).start(), firstToken(arm).start(), "| ", "")));
        }
        if (node.kind() == SyntaxKind.FN_DEF) {
            SyntaxNode lambda = Formatter.liftedLambda(node);
            if (lambda != null) {
                out.add(lifted(node, lambda));
            }
        }
        for (SyntaxElement e : node.children()) {
            if (e instanceof SyntaxNode child) {
                walk(child, out);
            }
        }
    }

    /**
     * The comma a node writes after its last member, if it has one.
     *
     * <p>A comma is that one where nothing follows it but what closes the run: a bracket, the arrow
     * of an example row's bindings, or the end of the node. Everywhere else what follows is another
     * member — which in some runs is a node and in others a bare name, so what is asked is what
     * comes after rather than what a member looks like.
     */
    private static java.util.Optional<SyntaxToken> trailingComma(SyntaxNode node) {
        List<SyntaxElement> written = new ArrayList<>();
        for (SyntaxElement e : node.children()) {
            if (e instanceof SyntaxNode || (e instanceof SyntaxToken t && !t.isTrivia()
                    && t.kind() != SyntaxKind.LINE_COMMENT && t.kind() != SyntaxKind.EOF)) {
                written.add(e);
            }
        }
        for (int i = 0; i < written.size(); i++) {
            if (!(written.get(i) instanceof SyntaxToken comma)
                    || comma.kind() != SyntaxKind.COMMA) {
                continue;
            }
            if (i + 1 == written.size()
                    || (written.get(i + 1) instanceof SyntaxToken next && closes(next.kind()))) {
                return java.util.Optional.of(comma);
            }
        }
        return java.util.Optional.empty();
    }

    /** The tokens that end a comma-separated run rather than standing inside one. */
    private static boolean closes(SyntaxKind kind) {
        return switch (kind) {
            case RPAREN, RBRACKET, RBRACE, GT, ARROW -> true;
            default -> false;
        };
    }

    /** A match's first arm, where the source wrote no bar in front of it. */
    private static java.util.Optional<SyntaxNode> firstArmWithoutItsBar(SyntaxNode match) {
        for (SyntaxElement e : match.children()) {
            if (e instanceof SyntaxToken t && t.kind() == SyntaxKind.PIPE) {
                return java.util.Optional.empty();   // the first thing of the arms is a bar
            }
            if (e instanceof SyntaxNode arm && arm.kind() == SyntaxKind.MATCH_CASE) {
                return java.util.Optional.of(arm);
            }
        }
        return java.util.Optional.empty();
    }

    /**
     * A definition written as a lambda, and the header the canonical form writes for it.
     *
     * <p>The stretch runs from the {@code =} to the lambda's {@code ->}, and what goes there is the
     * parameters and then the {@code =}. The parameters are copied as the source wrote them —
     * anything inside them is another rule's, and one of those rules is the comma this same pass
     * answers about.
     */
    private static Site lifted(SyntaxNode definition, SyntaxNode lambda) {
        SyntaxToken assign = definition.token(SyntaxKind.ASSIGN).orElseThrow();
        SyntaxToken arrow = lambda.token(SyntaxKind.ARROW).orElseThrow();
        int from = lambda.token(SyntaxKind.LPAREN).map(SyntaxToken::start).orElseGet(
                () -> firstParameter(lambda).start());
        String params = text(lambda, from, arrow.start()).strip();
        return new Site(Kind.A_DEFINITIONS_PARAMETERS, assign.start(), arrow.end(),
                (params.startsWith("(") ? params : "(" + params + ")") + " =",
                text(definition, assign.start(), arrow.end()));
    }

    /** A lambda's one bare parameter, for the {@code x -> e} form the canonical form parenthesises. */
    private static SyntaxToken firstParameter(SyntaxNode lambda) {
        for (SyntaxElement e : lambda.children()) {
            if (e instanceof SyntaxNode param) {
                return firstToken(param);
            }
        }
        throw new IllegalStateException("a lambda with no parameter");
    }

    private static SyntaxToken firstToken(SyntaxNode node) {
        for (SyntaxElement e : node.children()) {
            if (e instanceof SyntaxToken t && !t.isTrivia()) {
                return t;
            }
            if (e instanceof SyntaxNode child) {
                return firstToken(child);
            }
        }
        throw new IllegalStateException("a node with no token");
    }

    /** The source between two offsets, read from the tree the two came from. */
    private static String text(SyntaxNode node, int from, int to) {
        SyntaxNode root = node;
        while (root.parent() != null) {
            root = root.parent();
        }
        return root.text().substring(from - root.start(), to - root.start());
    }
}
