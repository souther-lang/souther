package souther.compiler.query;

import souther.compiler.ast.Hir;
import souther.compiler.check.ResolvedModule;
import souther.compiler.check.HelperInliner;
import souther.compiler.check.ValueCycles;
import souther.compiler.diag.CompileException;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The tree that is expanded is not the tree that was checked, and it is well founded too.
 *
 * <p>{@code Shapes.Expandable} answers of the module as resolution left it, and hands that tree over.
 * Every reader then makes another tree of it — derived, desugared, prepared, settled — and expands
 * that one. So what the refusal establishes is carried across four rewrites by nothing: each of them
 * could give a value a definition it did not have, and the answer that said the module was well
 * founded was about a tree none of them expanded.
 *
 * <p>What is pinned here is the observation and not the reason. Over a module written to give each
 * rewrite something to do, and one downstream of it, the values are still well founded in every tree
 * a compile makes. A rewrite that closed a cycle between two stages is caught here; one that added a
 * definition or an edge without closing a cycle is not. Whether the rewrites can do that at all is a
 * property of the rewrites, and nothing here says they cannot.
 *
 * <p>{@code ValueCycles.rejectIn} is what asks, because it is what the expansion relies on and there
 * is no second reading of well-foundedness to compare against. It is a check on a module as it was
 * written and it says more than this — a zero-parameter {@code let} whose body is a block is refused
 * by it too — so a tree failing it here is a report about that tree, and not on its own a statement
 * that every tree between the stages is a thing this check was meant to be handed.
 */
class EveryTreeAnExpansionIsGivenIsStillWellFoundedTest {

    /** Values read from a helper, from an invariant and from an example row, in a module with enough
     * declarations for every rewrite to have something to do. */
    private static final String UPSTREAM = """
            module m.a exposing ( Amount, base )

            data Amount = Int
                invariant value >= floor

            data Tag = Small | Large

            data In = { n: Int }
            data Out = { amount: Amount, tag: Tag }

            let floor = 0
            let base = 10
            let step = twice(2)
            let twice (n: Int) : Int = n * 2

            behavior go : (i: In) -> Out
                constructs Out, Amount
            let go (i) = Out { amount = Amount(i.n + step), tag = Small }

            example go
              | "a row" : (In { n = 1 }) -> Out { amount = Amount(5), tag = Small }
            """;

    /** And a module downstream, so a published value is one of the definitions in the table. */
    private static final String DOWNSTREAM = """
            module m.b
            import m.a ( Amount, base )

            data Req = { n: Int }
            data Quote = { amount: Amount }

            let markup = base + 5

            behavior quote : (r: Req) -> Quote
                constructs Quote, Amount
            let quote (r) = Quote { amount = Amount(r.n + markup) }
            """;

    private static Db dbOf() {
        return Compilation.ofDocuments(
                Map.of("a.sou", UPSTREAM, "b.sou", DOWNSTREAM), Set.of(), ModulePath.EMPTY).db();
    }

    /** Each tree a compile of {@code name} makes, by the stage that makes it. */
    private static Map<String, Hir.Module> treesOf(Db db, String name) {
        Map<String, Key<Hir.Module>> stages = new LinkedHashMap<>();
        // Resolution answers with the tree and the claim that it has been read, which the stages
        // below it hand on as an ordinary module.
        Answer<ResolvedModule> resolved = db.ask(new Names.Resolved(name));
        assertTrue(resolved.present(), "resolved of " + name + ": " + resolved.reports());
        stages.put("derived", new Shapes.Derived(name));
        stages.put("desugared", new Shapes.Desugared(name));
        stages.put("prepared", new Shapes.Prepared(name));
        stages.put("settled", new Bodies.Settled(name));
        Map<String, Hir.Module> out = new LinkedHashMap<>();
        out.put("resolved", resolved.value().module());
        stages.forEach((stage, key) -> {
            Answer<Hir.Module> answer = db.ask(key);
            assertTrue(answer.present(), stage + " of " + name + ": " + answer.reports());
            out.put(stage, answer.value());
        });
        return out;
    }

    private static Map<String, Hir.FnDef> publishedTo(Db db, String name) {
        Answer<Map<String, Hir.FnDef>> imported = db.ask(new Bodies.ImportedDefinitions(name));
        return imported.present() ? imported.value() : Map.of();
    }

    @Test
    void valueWellFoundednessSurvivesTheRewritesBeforeAnExpansion() {
        Db db = dbOf();
        Map<String, String> aValueOf = Map.of("m.a", "step", "m.b", "markup");
        aValueOf.forEach((name, value) -> {
            Map<String, Hir.FnDef> published = publishedTo(db, name);
            treesOf(db, name).forEach((stage, tree) -> {
                // a value is still there to be asked about, so a stage that dropped the ones this
                // module was written around is not passing by having nothing left to walk
                assertTrue(HelperInliner.helpersOf(tree).containsKey(value),
                        "the " + stage + " tree of " + name + " no longer declares `" + value + "`");
                assertDoesNotThrow(() -> ValueCycles.rejectIn(tree, published),
                        "the " + stage + " tree of " + name + " is expanded, and its values reach"
                                + " themselves");
            });
        });
    }

    /** And the stages are not one tree asked for five times. */
    @Test
    void theTreesAreDifferentTrees() {
        Map<String, Hir.Module> trees = treesOf(dbOf(), "m.a");

        assertNotEquals(trees.get("resolved"), trees.get("settled"),
                "nothing was rewritten between the tree that was checked and the tree expanded");
    }

    /**
     * And the check said something about those trees. Asked of a tree with a value that does reach
     * itself, it refuses — so a stage that passes above passed on its own account.
     */
    @Test
    void theSameQuestionAskedOfATreeWithACycleRefusesIt() {
        Db db = Compilation.ofDocuments(Map.of("a.sou", """
                module m.a

                data In = { n: Int }
                data Out = { n: Int }

                let step = step

                behavior go : (i: In) -> Out
                    constructs Out
                let go (i) = Out { n = i.n + step }
                """), Set.of(), ModulePath.EMPTY).db();
        Answer<ResolvedModule> resolved = db.ask(new Names.Resolved("m.a"));
        assertTrue(resolved.present(), "resolution answers; the refusal comes later");

        assertThrows(CompileException.class,
                () -> ValueCycles.rejectIn(resolved.value().module(), Map.of()));
    }
}
