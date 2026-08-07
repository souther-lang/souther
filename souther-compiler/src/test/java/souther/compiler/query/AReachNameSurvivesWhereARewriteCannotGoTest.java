package souther.compiler.query;

import souther.compiler.ast.Ast;
import souther.compiler.meta.ModulePath;
import souther.compiler.types.ReachName;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a body says when it leaves the module it was written in, in the one place no walk over an
 * expression reaches.
 *
 * <p>A function argument stands in {@code Ast.Expansion.given}, and that is not a slot
 * ({@code Ast.atSlots}): a callee that applies its argument holds the same lambda inside its body,
 * so a walk taking both would read one lambda twice. A published body is closed by the module that
 * declares it and read against the reader's declarations, and the rewrite that does the closing goes
 * through that walk — so what stands in {@code given} was left behind, saying what it said where it
 * was written.
 *
 * <p>{@code lib.flatten} recurses, so it is a method rather than an expression and its call inside
 * the lambda stays a call. In {@code lib} that call is reached bare; in {@code app}, which emits the
 * method as its own, it is reached under {@code lib}. Both names are for one declaration and the
 * reader's is the one a table here is keyed by.
 */
class AReachNameSurvivesWhereARewriteCannotGoTest {

    private static final String LIB = """
            module lib exposing ( Node, flatten )

            data Node = { n: Int, kids: List<Node> }

            let flatten (t: Node): List<Int> = [t.n] ++ List.flatMap(k -> flatten(k), t.kids)
            """;

    private static final String APP = """
            module app exposing ( Out, go )

            import lib ( Node, flatten )

            data Out = { xs: List<Int> }

            behavior go : (t: Node) -> Out constructs Out
            let go (t) = Out { xs = flatten(t) }
            """;

    /** The imported recursive helper as {@code app} emits it: a method of its own. */
    private static Ast.Expr taken() {
        Map<String, String> byId = new LinkedHashMap<>();
        byId.put("lib.sou", LIB);
        byId.put("app.sou", APP);
        Compilation c = Compilation.ofDocuments(byId, Set.of(), ModulePath.EMPTY);
        Ast.FnDef def = c.db().ask(new Bodies.LoweredBody("app", "lib.flatten")).value();
        return ((Ast.FnBody.Written) def.body()).expr();
    }

    /** Every application a walk over the slots reaches. */
    private static List<Ast.Apply> throughTheSlots(Ast.Expr e) {
        List<Ast.Apply> out = new ArrayList<>();
        if (e instanceof Ast.Apply call) {
            out.add(call);
        }
        Ast.forEachChild(e, c -> out.addAll(throughTheSlots(c)));
        return out;
    }

    /** Every application standing in what a combinator was handed, which the walk above does not
     * reach — collected by hand, because that is the point. */
    private static List<Ast.Apply> inWhatWasHandedOver(Ast.Expr e) {
        List<Ast.Apply> out = new ArrayList<>();
        if (e instanceof Ast.Expansion ex) {
            for (Ast.Given g : ex.given()) {
                out.addAll(throughTheSlots(g.value()));
                out.addAll(inWhatWasHandedOver(g.value()));
            }
        }
        Ast.forEachChild(e, c -> out.addAll(inWhatWasHandedOver(c)));
        return out;
    }

    /**
     * The premise. Without a call standing there the rest would pass by finding nothing, and without
     * the walk missing it the rewrite would have reached it like anything else.
     *
     * <p>The callee does apply what it was handed, so the expansion's body holds a call of its own —
     * a different node, reached and rewritten like anything in a slot. The one asked about below is
     * the node in {@code given}, and it is reached by neither.
     */
    @Test
    void theCallStandsWhereAWalkOverTheSlotsDoesNotReach() {
        Ast.Expr body = taken();
        List<Ast.Apply> handed = calls(inWhatWasHandedOver(body));

        assertEquals(1, handed.size(),
                "the recursive helper is called inside the lambda handed to the combinator");
        assertTrue(calls(throughTheSlots(body)).stream().noneMatch(call -> call == handed.get(0)),
                "and no walk over the slots reaches that node");
    }

    /** And it is reached by the name the module reading it reaches it by, though the rewrite that
     * settles that name goes through a walk which never arrives there. */
    @Test
    void andItIsReachedByTheNameTheReaderReachesItBy() {
        assertEquals(List.of(new ReachName.OfModule("lib", "flatten")),
                calls(inWhatWasHandedOver(taken())).stream().map(Ast.Apply::reachedAs).toList(),
                "reached under the module that declares it, which is how `app` keys the method");
    }

    private static List<Ast.Apply> calls(List<Ast.Apply> found) {
        return found.stream()
                .filter(call -> call.denotes() != null && call.denotes().name().equals("flatten"))
                .toList();
    }
}
