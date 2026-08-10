package souther.compiler.cst;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A field-access chain follows any identifier-led primary, not only a bare name (issue #158). What
 * keeps it apart from the bare `.field` getter (ADR-0055) is where each sits: a getter opens an
 * expression, a read follows one, and the two never compete for the same position.
 */
class CstCallResultFieldAccessTest {

    private static SyntaxNode parsed(String body) {
        String src = "module demo\n"
                + "data In = { n: Int }\n"
                + "data Out = { m: Int }\n"
                + "let run (i) = " + body + "\n";
        CstParser.Result r = CstParser.parse(src);
        assertTrue(r.errors().isEmpty(), () -> "unexpected syntax errors: " + r.errors());
        return r.root();
    }

    /** Every node of {@code kind} in the tree, outermost first. */
    private static List<SyntaxNode> allOf(SyntaxNode n, SyntaxKind kind) {
        List<SyntaxNode> out = new ArrayList<>();
        if (n.kind() == kind) {
            out.add(n);
        }
        for (SyntaxNode c : n.childNodes()) {
            out.addAll(allOf(c, kind));
        }
        return out;
    }

    private static SyntaxNode onlyOf(SyntaxNode n, SyntaxKind kind) {
        List<SyntaxNode> found = allOf(n, kind);
        assertEquals(1, found.size(), () -> "expected one " + kind + ", found " + found.size());
        return found.get(0);
    }

    @Test
    void aCallResultCarriesTheFieldAccess() {
        SyntaxNode access = onlyOf(parsed("amountOf(i).value"), SyntaxKind.FIELD_ACCESS);

        assertEquals(SyntaxKind.APPLY_EXPR, access.childNodes().get(0).kind());
        assertEquals("amountOf(i).value", access.text().strip());
    }

    /**
     * A qualified callee is a read like any other, and the argument list is written after it. The
     * outermost read is the one the call's result carries; the inner one is how the name was
     * written. Which of the two {@code up.amountOf} is — a member of a namespace or a field taken
     * off a binding named {@code up} — is not a question the parser answers (issue #274).
     */
    @Test
    void aQualifiedCallIsAnArgumentListAfterAReadAndTheResultCarriesAnother() {
        List<SyntaxNode> reads = allOf(parsed("up.amountOf(i).value"), SyntaxKind.FIELD_ACCESS);

        assertEquals(2, reads.size(), () -> "expected the callee's read and the result's, found " + reads);
        assertEquals("up.amountOf(i).value", reads.get(0).text().strip());
        assertEquals(SyntaxKind.APPLY_EXPR, reads.get(0).childNodes().get(0).kind());
        assertEquals("up.amountOf", reads.get(1).text().strip());
    }

    @Test
    void aBareGetterInArgumentPositionIsStillAGetter() {
        SyntaxNode root = parsed("pick(amountsOf(i), .value)");

        assertEquals(1, allOf(root, SyntaxKind.FIELD_GETTER).size(), "the `.value` argument is a getter");
        assertEquals(0, allOf(root, SyntaxKind.FIELD_ACCESS).size(), "nothing is read off the call");
    }

    @Test
    void aChainOfReadsFollowsACall() {
        SyntaxNode outer = allOf(parsed("personOf(i).address.city"), SyntaxKind.FIELD_ACCESS).get(0);

        assertEquals("personOf(i).address.city", outer.text().strip());
        assertEquals(SyntaxKind.FIELD_ACCESS, outer.childNodes().get(0).kind());
        assertEquals("personOf(i).address", outer.childNodes().get(0).text().strip());
    }

    /**
     * An argument list begins on the line its callee ends on. The specification says so of every
     * application; before this it held only where the callee was not a bare or qualified name, so
     * the same two lines meant one thing written one way and another written the other. The block
     * these are written in has a result of its own, so what a next-line `(` opens is a parenthesised
     * expression that stands as a statement's value rather than an argument list.
     */
    @ParameterizedTest
    @ValueSource(strings = {
            "amountOf",                 // a bare name
            "up.amountOf",              // a qualified name
            "amountOf // a comment",    // a comment between the two
            "amountOf(i)",              // the result of an application
    })
    void aLineBreakEndsThePostfixChainWhateverTheCalleeIs(String callee) {
        SyntaxNode root = parsed("{\n    let a = " + callee + "\n    (i)\n}");

        assertEquals(0, allOf(root, SyntaxKind.APPLY_EXPR).stream()
                        .filter(n -> n.text().strip().endsWith("(i)")
                                && n.text().contains("\n")).count(),
                () -> "the next line's `(i)` was applied to `" + callee + "`");
        assertEquals(1, allOf(root, SyntaxKind.PAREN_EXPR).size(),
                () -> "`(i)` is a parenthesised expression after `" + callee + "`");
    }
}
