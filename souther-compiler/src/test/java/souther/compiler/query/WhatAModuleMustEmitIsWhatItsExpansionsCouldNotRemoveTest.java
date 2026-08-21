package souther.compiler.query;

import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;
import java.util.SequencedSet;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which recursive helpers a module has to process and emit, answered from what its expansions did.
 *
 * <p>Every tree the module is made of is expanded somewhere, and each expansion answers with the
 * recursions it could not remove. Joined and closed over the call graph, that is the set. The answer
 * it replaces was a prediction: a walk listing the places a module writes expressions, made before
 * any of those expansions ran, and it did not list {@code ensures}.
 *
 * <p>The cases below are the ones the prediction was right about — a fold in a {@code let}, in an
 * {@code invariant}, in an example row, a recursion the module declared — and the one it was wrong
 * about, which is a module whose only reach to a quantifier is a rule. They are here together
 * because what has to hold is that moving the answer changed nothing except the last.
 */
class WhatAModuleMustEmitIsWhatItsExpansionsCouldNotRemoveTest {

    private static Db dbOf(String module, String source) {
        return Compilation.ofDocuments(Map.of(module + ".sou", source), Set.of(), ModulePath.EMPTY)
                .db();
    }

    private static SequencedSet<String> required(Db db, String module) {
        Answer<SequencedSet<String>> answer = db.ask(new Bodies.RequiredRecursiveDefs(module));
        assertTrue(answer.present(), "required of " + module + ": " + answer.reports());
        return answer.value();
    }

    /** A fold in a `let`. */
    @Test
    void aFoldInADefinitionIsRequired() {
        Db db = dbOf("inlet", """
                module inlet

                let total (xs: List<Int>) : Bool = List.all(x -> x >= 0, xs)
                """);

        assertEquals(Set.of("List.foldFrom"), required(db, "inlet"));
    }

    /** And in an `invariant`. */
    @Test
    void aFoldInAnInvariantIsRequired() {
        Db db = dbOf("ininv", """
                module ininv

                data AllPos = List<Int>
                    invariant List.all(x -> x >= 0, value)
                """);

        assertEquals(Set.of("List.foldFrom"), required(db, "ininv"));
    }

    /** And in an example row. */
    @Test
    void aFoldInARowIsRequired() {
        Db db = dbOf("inrow", """
                module inrow

                data Flag = { on: Bool }

                behavior mark : (xs: List<Int>) -> Flag
                let mark (xs) = Flag { on = true }

                example mark
                    | "a row folds" : ([ 1, 2 ]) -> Flag { on = List.all(x -> x >= 0, [ 1 ]) }
                """);

        assertTrue(required(db, "inrow").contains("List.foldFrom"), required(db, "inrow").toString());
    }

    /** A recursion the module declared is its own to check and publish, reached or not. */
    @Test
    void aDeclaredRecursionIsRequiredWhetherOrNotAnythingReachesIt() {
        Db db = dbOf("owned", """
                module owned exposing ( Emp, depth )

                data Emp = { boss: Emp? }

                let depth (e: Emp) : Int =
                    match e.boss with
                        | Some b -> 1 + depth(b)
                        | None   -> 0
                """);

        assertEquals(Set.of("depth"), required(db, "owned"));
    }

    /** A module that folds nowhere needs nothing. */
    @Test
    void aModuleThatFoldsNowhereRequiresNothing() {
        Db db = dbOf("plain", """
                module plain

                data Count = Int

                behavior countIt : (n: Int) -> Count
                let countIt (n) = Count { value = n }
                """);

        assertEquals(Set.of(), required(db, "plain"));
    }

    /**
     * Nothing is emitted before the module is lowered. What it emits follows from expanding its
     * trees, so a stage that has not expanded them has nothing to say about it — and the prediction
     * that used to be written here answered before any of them had run.
     */
    @Test
    void aModuleCarriesNoEmissionListUntilItIsLowered() {
        Db db = dbOf("inlet", """
                module inlet

                let total (xs: List<Int>) : Bool = List.all(x -> x >= 0, xs)
                """);

        assertEquals(List.of(), db.ask(new Bodies.Settled("inlet")).value().takenOn(),
                "a settled module takes nothing on");
        assertEquals(Set.of("List.foldFrom"),
                db.ask(new Bodies.Lowering("inlet")).value().lowered().takenOn().stream()
                        .map(souther.compiler.ast.Hir.FnDef::name)
                        .collect(java.util.stream.Collectors.toSet()),
                "and the lowered one carries what its expansions could not remove");
    }

    /**
     * And the case the prediction was wrong about: a rule is the module's only reach to a fold. The
     * fold is required, and the walk that listed where a module writes expressions said nothing was.
     */
    @Test
    void aFoldReachedOnlyFromARuleIsRequired() {
        Db db = dbOf("inrule", """
                module inrule

                data Count = Int

                behavior countIt : (xs: List<Int>) -> Count
                    ensures List.all(x -> x >= 0, xs) && value.value >= 0
                """);

        assertEquals(Set.of("List.foldFrom"), required(db, "inrule"));
    }
}
