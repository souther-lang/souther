package souther.compiler.query;

import souther.compiler.Compiler;
import souther.compiler.ast.Hir;
import souther.compiler.check.ResolvedModule;
import souther.compiler.check.HelperInliner;
import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a module declares is what its source wrote, whichever stage is asked.
 *
 * <p>A module emits the recursive helpers it reaches as methods of its own, and {@link
 * Shapes.Prepared} put them into the same list its declarations are in. From there on one question
 * had two answers: before that pass {@code helpersOf} said what the module declared, and after it,
 * that plus what the module took on to emit. Every reader that wanted the first — which is the
 * {@code exposing} check, the value namespace a body is resolved against, what the module publishes
 * — got whichever the caller above it happened to hold.
 *
 * <p>The two are separate components of the module now, so a stage that adds to one does not answer
 * for the other.
 */
class WhatAModuleDeclaresDoesNotChangeWithTheStageTest {

    /** `flatten` recurses, so a reader has to emit it as a method of its own; `own` folds, which
     * reaches the library's recursive `List.foldFrom` and is taken on the same way. */
    private static final String LIB = """
            module lib exposing ( flatten )

            let flatten (xs: List<List<Int>>) : List<Int> =
                if List.isEmpty(xs) then []
                else List.head(xs, []) ++ flatten(List.drop(1, xs))
            """;

    private static final String APP = """
            module app exposing ( own )

            import lib ( flatten )

            let own (xs: List<Int>) : List<Int> = List.map({ (x) -> x + 1 }, xs)
            let both (xs: List<List<Int>>) : List<Int> = own(flatten(xs))
            """;

    private static Db db() {
        return Compilation.ofDocuments(
                Map.of("lib.sou", LIB, "app.sou", APP), Set.of(), ModulePath.EMPTY).db();
    }

    /** Every stage that hands a module over, by the name of the stage. */
    private static Map<String, Hir.Module> stagesOf(Db db, String name) {
        Map<String, Key<Hir.Module>> keys = new LinkedHashMap<>();
        // Resolution answers with the tree and the claim that it has been read, which the stages
        // below it hand on as an ordinary module.
        Answer<ResolvedModule> resolved = db.ask(new Names.Resolved(name));
        assertTrue(resolved.present(), "resolved of " + name + ": " + resolved.reports());
        keys.put("derived", new Shapes.Derived(name));
        keys.put("desugared", new Shapes.Desugared(name));
        keys.put("prepared", new Shapes.Prepared(name));
        keys.put("settled", new Bodies.Settled(name));
        Map<String, Hir.Module> out = new LinkedHashMap<>();
        out.put("resolved", resolved.value().module());
        keys.forEach((stage, key) -> {
            Answer<Hir.Module> answer = db.ask(key);
            assertTrue(answer.present(), stage + " of " + name + ": " + answer.reports());
            out.put(stage, answer.value());
        });
        return out;
    }

    @Test
    void everyStageSaysTheModuleDeclaresWhatItsSourceWrote() {
        Db db = db();
        stagesOf(db, "app").forEach((stage, module) ->
                assertEquals(Set.of("own", "both"), HelperInliner.helpersOf(module).keySet(),
                        "the " + stage + " tree of `app` disagrees about what it declares"));
    }

    /**
     * And this module does take helpers on, so no stage passes by having none to confuse a
     * declaration with. Asked of what the module emits, which is a different question and a different
     * answer.
     */
    @Test
    void theModuleTakesOnHelpersItDidNotDeclare() {
        Db db = db();
        assertEquals(Set.of("List.foldFrom", "lib.flatten"),
                db.ask(new Bodies.RecursiveHelpers("app")).value());
    }

    /**
     * Which of the two a fn is in is what the declaration says of it, at every stage.
     *
     * <p>Asked of {@link Hir.FnDef#declaredBy} and not of the names. A reach name carries a dot and a
     * source identifier cannot, so the two key sets never meet whatever the components hold — a test
     * written over the names would pass however wrongly a pass filed one.
     */
    @Test
    void eachComponentHoldsWhatItsNameSays() {
        Db db = db();
        stagesOf(db, "app").forEach((stage, module) -> {
            module.fns().forEach(fn -> assertTrue(fn.declaredBy("app"),
                    "the " + stage + " tree of `app` has `" + fn.name() + "` among its declarations,"
                            + " and " + fn.declaredIn() + " declared it"));
            module.takenOn().forEach(fn -> assertFalse(fn.declaredBy("app"),
                    "the " + stage + " tree of `app` took on `" + fn.name() + "`, which it declared"));
        });
    }

    /**
     * A row applies a published helper that does not recurse. It is taken on for that reason alone —
     * a row runs a helper rather than expanding it (ADR-0077) — so what a module takes on is not only
     * what it reaches recursively, and a component holding only the recursive ones would drop it.
     */
    @Test
    void aHelperOnlyARowAppliesIsTakenOnToo() {
        Db db = Compilation.ofDocuments(Map.of("rules.sou", """
                module rules exposing ( doubled )

                let doubled (n: Int) : Int = n * 2
                """, "app.sou", """
                module app exposing ( In, Out, run )

                import rules ( doubled )

                data In  = { n: Int }
                data Out = { m: Int }

                behavior run : (i: In) -> Out constructs Out
                let run (i) = Out { m = i.n }

                example run
                    | "a row applies a published helper" : (In { n = doubled(3) }) -> Out { m = 6 }
                """), Set.of(), ModulePath.EMPTY).db();

        Hir.Module prepared = db.ask(new Shapes.Prepared("app")).value();
        // `run` implements a behavior, which is not a helper and is lowered on its own.
        assertEquals(Set.of(), HelperInliner.helpersOf(prepared).keySet());
        assertEquals(Set.of("rules.doubled"), HelperInliner.takenOnBy(prepared).keySet());
        assertEquals(Set.of(), db.ask(new Bodies.RecursiveHelpers("app")).value(),
                "nothing here recurses, so this is the row's doing and not a recursion's");
        assertEquals(Set.of("rules.doubled"),
                db.ask(new Bodies.Lowering("app")).value().lowered().takenOn().stream()
                        .map(Hir.FnDef::name).collect(java.util.stream.Collectors.toSet()));
    }

    /**
     * The same, with the row in an attached {@code examples for} file. That is the shape the two
     * rebuilds that run either side of the pass filling {@code takenOn} are on — the one that gathers
     * an attached file's rows into the module, and the one that keeps only the rows of one file to
     * report against it — and the row still finds the method.
     */
    @Test
    void anAttachedFilesRowStillReachesWhatTheModuleTookOn() {
        assertDoesNotThrow(() -> Compiler.compileModules(List.of("""
                module rules exposing ( doubled )

                let doubled (n: Int) : Int = n * 2
                """, """
                module app exposing ( In, Out, run )

                import rules ( doubled )

                data In  = { n: Int }
                data Out = { m: Int }

                behavior run : (i: In) -> Out constructs Out
                let run (i) = Out { m = i.n }
                """, """
                examples for app

                example run
                    | "written beside the model" : (In { n = doubled(3) }) -> Out { m = 6 }
                """)));
    }

    /** And the lowered tree the backend emits from keeps them apart, which is the last place a pass
     * could put a taken-on helper where a declaration goes. */
    @Test
    void theTreeTheBackendEmitsFromKeepsThemApart() {
        Db db = db();
        Hir.Module lowered = db.ask(new Bodies.Lowering("app")).value().lowered();

        lowered.fns().forEach(fn -> assertTrue(fn.declaredBy("app"),
                "`" + fn.name() + "` is emitted as a declaration of `app`, and "
                        + fn.declaredIn() + " declared it"));
        assertEquals(Set.of("List.foldFrom", "lib.flatten"),
                lowered.takenOn().stream().map(Hir.FnDef::name)
                        .collect(java.util.stream.Collectors.toSet()));
    }
}
