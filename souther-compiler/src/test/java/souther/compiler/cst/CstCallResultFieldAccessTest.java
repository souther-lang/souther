package souther.compiler.cst;

import org.junit.jupiter.api.Test;

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

        assertEquals(SyntaxKind.CALL_EXPR, access.childNodes().get(0).kind());
        assertEquals("amountOf(i).value", access.text().strip());
    }

    @Test
    void aQualifiedCallIsTheCallAndNotAFieldReadOnTheModule() {
        SyntaxNode access = onlyOf(parsed("up.amountOf(i).value"), SyntaxKind.FIELD_ACCESS);

        // one FIELD_ACCESS only: `up.amountOf` is the call's name, so `.value` is the sole read
        assertEquals(SyntaxKind.CALL_EXPR, access.childNodes().get(0).kind());
        assertEquals("up.amountOf(i)", access.childNodes().get(0).text().strip());
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
}
