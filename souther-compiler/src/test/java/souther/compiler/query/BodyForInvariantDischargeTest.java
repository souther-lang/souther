package souther.compiler.query;

import souther.compiler.ast.Ast;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The invariant-discharge analysis reads its own representation of a body, and what makes it its own
 * is which abstractions are still there.
 *
 * <p>The tree the backend emits has been expanded until nothing it cannot emit is left, so a
 * {@code List.map} in it is the fold that {@code List.map} is. A rule about what {@code List.map}
 * does to a length has nothing to match there, which is how the analysis came to hold a table of
 * combinator rules that could not fire. These pin the two apart.
 */
class BodyForInvariantDischargeTest {

    private static final String SOURCE = """
            module m.a
            data Money = Decimal
                invariant value >= 0m
            data Bag = { items: List<Money> }
            let doubled (x: Money): Money = x + x
            behavior shift : (b: Bag) -> List<Money>
            let shift (b) = List.map(x -> doubled(x), b.items)
            """;

    private static Ast.Expr body(Key<Ast.FnDef> key) {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("a.sou", SOURCE);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        return c.db().ask(key).value().written();
    }

    private static List<String> calls(Ast.Expr e) {
        List<String> out = new ArrayList<>();
        collect(e, out);
        return out;
    }

    private static void collect(Ast.Expr e, List<String> out) {
        if (e instanceof Ast.Apply call) {
            out.add(call.written());
        }
        Ast.forEachChild(e, child -> collect(child, out));
    }

    @Test
    void theAnalysisBodyKeepsTheOperationsTheLanguageDefines() {
        List<String> fns = calls(body(new Bodies.BodyForInvariantDischarge("m.a", "shift")));
        assertTrue(fns.contains("List.map"),
                "a standard-library operation is what the rules are written about: " + fns);
    }

    @Test
    void theAnalysisBodyExpandsTheModulesOwnHelpers() {
        List<String> fns = calls(body(new Bodies.BodyForInvariantDischarge("m.a", "shift")));
        assertFalse(fns.contains("doubled"),
                "a helper of this module carries no such rule, and does not travel: " + fns);
    }

    @Test
    void theEmittedBodyHasExpandedTheOperationAway() {
        List<String> fns = calls(body(new Bodies.LoweredBody("m.a", "shift")));
        assertFalse(fns.contains("List.map"),
                "the backend emits folds, not operations: " + fns);
    }
}
