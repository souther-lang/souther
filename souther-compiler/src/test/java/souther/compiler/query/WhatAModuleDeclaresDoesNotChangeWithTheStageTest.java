package souther.compiler.query;

import souther.compiler.Compiler;
import souther.compiler.ast.DefinitionRole;
import souther.compiler.ast.Hir;
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
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
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
            module app exposing ( own, Bag, run )

            import lib ( flatten )

            data Bag = List<Int>

            let own (xs: List<Int>) : List<Int> = List.map({ (x) -> x + 1 }, xs)
            let both (xs: List<List<Int>>) : List<Int> = own(flatten(xs))

            behavior run : (xs: List<List<Int>>) -> Bag constructs Bag
            let run (xs) = Bag { value = both(xs) }
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
        Answer<Hir.Module> resolved = db.ask(new Names.Resolved(name));
        assertTrue(resolved.present(), "resolved of " + name + ": " + resolved.reports());
        // The derived stage answers with the module where every declaration came out; what is asked
        // about here is the tree it holds, which is a question about the payload and not about that.
        Answer<souther.compiler.check.Derived.Module> derived = db.ask(new Shapes.Derived(name));
        assertTrue(derived.present(), "derived of " + name + ": " + derived.reports());
        Answer<souther.compiler.check.Desugared.Module> desugared =
                db.ask(new Shapes.Desugared(name));
        assertTrue(desugared.present(), "desugared of " + name + ": " + desugared.reports());
        Answer<souther.compiler.check.Prepared> prepared = db.ask(new Shapes.Prepared(name));
        assertTrue(prepared.present(), "prepared of " + name + ": " + prepared.reports());
        keys.put("settled", new Bodies.Settled(name));
        Map<String, Hir.Module> out = new LinkedHashMap<>();
        out.put("resolved", resolved.value());
        out.put("derived", derived.value().tree());
        out.put("desugared", desugared.value().tree());
        out.put("prepared", prepared.value().tree());
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
     * And this module does emit helpers it did not declare, so no stage passes by having none to
     * confuse a declaration with. What it emits is a different question from what it declares, and
     * it is answered after its trees have been expanded rather than before: a recursion is emitted
     * here because an expansion of this module could not remove a call to it.
     */
    @Test
    void theModuleEmitsHelpersItDidNotDeclare() {
        Db db = db();
        Set<String> emitted = new java.util.LinkedHashSet<>();
        db.ask(new Bodies.RequiredRecursiveDefs("app")).value()
                .forEach(reference -> emitted.add(reference.rendered()));
        assertEquals(Set.of("List.foldFrom", "lib.flatten"), emitted);
        assertEquals(Set.of("own", "both"),
                HelperInliner.helpersOf(db.ask(new Bodies.Settled("app")).value()).keySet(),
                "and what it declares is unchanged by that");
    }

    /**
     * Which of the two a fn is in is what the fn says of itself, at every stage.
     *
     * <p>Asked of {@link Hir.FnDef#declaredBy} and {@link Hir.FnDef#role}, not of the names. A reach
     * name carries a dot and a source identifier cannot, so the two key sets never meet whatever the
     * components hold — a test written over the names would pass however wrongly a pass filed one.
     *
     * <p>Two things are taken on and only one of them is another module's. A method minted for a
     * row's operand is emitted into this module's own program and is declared by it, so the
     * declaring module does not tell that one from a declaration; what it is does.
     */
    @Test
    void eachComponentHoldsWhatItsFnsSayTheyAre() {
        Db db = db();
        stagesOf(db, "app").forEach((stage, module) -> {
            module.fns().forEach(fn -> {
                assertTrue(fn.declaredBy("app"),
                        "the " + stage + " tree of `app` has `" + fn.name() + "` among its"
                                + " declarations, and " + fn.declaredIn() + " declared it");
                assertInstanceOf(DefinitionRole.Ordinary.class, fn.role(),
                        "the " + stage + " tree of `app` declares `" + fn.name() + "`");
            });
            module.takenOn().forEach(fn -> assertTrue(
                    !fn.declaredBy("app") || fn.role() instanceof DefinitionRole.RowValue,
                    "the " + stage + " tree of `app` took on `" + fn.name() + "`, which it declared"
                            + " and which is not one of its rows' values"));
        });
    }

    /**
     * A row is emitted as a method per operand, and the helper the row names is not one of them: the
     * operand is a definition of this module and the call in it is expanded into it, the way a call
     * in a body is. So nothing is taken on for a row at all.
     *
     * <p>The row's own methods are a family of their own and not among what the module holds. A row
     * operand is reached from a row and from nothing a source can spell, so it is no declaration a
     * name resolves to — and it is told from one by what it was made as. Its declaration cannot tell
     * them apart: this module is what declared it, so {@link Hir.FnDef#declaredIn} says the same of
     * both, and the shape of its name says nothing either.
     */
    @Test
    void aRowIsEmittedAsItsOwnMethodsAndNothingIsTakenOnForIt() {
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

        souther.compiler.check.Prepared state = db.ask(new Shapes.Prepared("app")).value();
        Hir.Module prepared = state.tree();
        // `run` implements a behavior, which is not a helper and is lowered on its own.
        assertEquals(Set.of(), HelperInliner.helpersOf(prepared).keySet());
        // A method per row operand — the row's input and its expected value each run as one — read
        // off the correspondence the preparation constructed rather than spelled here.
        Set<String> rowMethods = Set.copyOf(state.operandMethods().values());
        assertEquals(2, rowMethods.size(), "one input and one expectation, each emitted for the row");
        assertEquals(Set.of(), HelperInliner.takenOnBy(prepared).keySet(),
                "`rules.doubled` is expanded into the operand, and nothing is taken on beside it");
        assertEquals(rowMethods, db.ask(new Bodies.RowFixtureDefs("app")).value().keySet(),
                "the operands' methods are their own family");
        // And not in the table a call expands against. Nothing a source can write reaches one, so a
        // name has nothing to resolve to there — and every rule keyed on what that table holds had a
        // synthetic method among its subjects while it did.
        souther.compiler.check.HelperTable table =
                db.ask(new Bodies.Expanding("app", souther.compiler.check.InliningPolicy.FULL))
                        .value().table();
        rowMethods.forEach(method -> assertFalse(
                table.reaches(new souther.compiler.types.ReachName.Own(
                        new souther.compiler.types.ValueName.Helper("app", method))),
                method + " is reachable by name"));
        assertEquals(Set.of(), Set.copyOf(db.ask(new Bodies.RequiredRecursiveDefs("app")).value()),
                "and nothing here recurses, so nothing else needs a method");
        assertEquals(rowMethods,
                db.ask(new Bodies.Lowering("app")).value().lowered().takenOn().stream()
                        .map(Hir.FnDef::name).collect(java.util.stream.Collectors.toSet()));
        // Each of them says what it is. The declaration cannot: this module is what declared them.
        db.ask(new Bodies.RowFixtureDefs("app")).value().values().forEach(fn -> {
            assertTrue(fn.declaredBy("app"), fn.name() + " is emitted into `app`'s own program");
            assertInstanceOf(DefinitionRole.RowValue.class, fn.role(), fn.name());
        });
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
