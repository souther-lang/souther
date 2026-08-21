package souther.compiler.query;

import souther.compiler.meta.ModulePath;

import org.junit.jupiter.api.Test;

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
 * <p>So the two are held against each other here. Where the prediction was right they agree, and the
 * cases below are the ones it was right about — a fold in a {@code let}, in an {@code invariant}, in
 * an example row, a recursion the module declared. Where it was wrong they differ, and the
 * difference is the whole of what this changes.
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

    private static SequencedSet<String> predicted(Db db, String module) {
        return db.ask(new Bodies.RecursiveHelpers(module)).value();
    }

    /** A fold in a `let`, which the walk did list. */
    @Test
    void aFoldInADefinitionIsFoundBothWays() {
        Db db = dbOf("inlet", """
                module inlet

                let total (xs: List<Int>) : Bool = List.all(x -> x >= 0, xs)
                """);

        assertEquals(Set.of("List.foldFrom"), required(db, "inlet"));
        assertEquals(predicted(db, "inlet"), required(db, "inlet"));
    }

    /** And in an `invariant`, which it also listed. */
    @Test
    void aFoldInAnInvariantIsFoundBothWays() {
        Db db = dbOf("ininv", """
                module ininv

                data AllPos = List<Int>
                    invariant List.all(x -> x >= 0, value)
                """);

        assertEquals(Set.of("List.foldFrom"), required(db, "ininv"));
        assertEquals(predicted(db, "ininv"), required(db, "ininv"));
    }

    /** And in an example row. */
    @Test
    void aFoldInARowIsFoundBothWays() {
        Db db = dbOf("inrow", """
                module inrow

                data Flag = { on: Bool }

                behavior mark : (xs: List<Int>) -> Flag
                let mark (xs) = Flag { on = true }

                example mark
                    | "a row folds" : ([ 1, 2 ]) -> Flag { on = List.all(x -> x >= 0, [ 1 ]) }
                """);

        assertTrue(required(db, "inrow").contains("List.foldFrom"), required(db, "inrow").toString());
        assertEquals(predicted(db, "inrow"), required(db, "inrow"));
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
        assertEquals(predicted(db, "owned"), required(db, "owned"));
    }

    /** A module that folds nowhere needs nothing, and neither answer says otherwise. */
    @Test
    void aModuleThatFoldsNowhereRequiresNothing() {
        Db db = dbOf("plain", """
                module plain

                data Count = Int

                behavior countIt : (n: Int) -> Count
                let countIt (n) = Count { value = n }
                """);

        assertEquals(Set.of(), required(db, "plain"));
        assertEquals(predicted(db, "plain"), required(db, "plain"));
    }

    /**
     * And the case the prediction was wrong about: a rule is the module's only reach to a fold. The
     * fold is required, and the walk said nothing was.
     */
    @Test
    void aFoldReachedOnlyFromARuleIsRequiredAndWasNotPredicted() {
        Db db = dbOf("inrule", """
                module inrule

                data Count = Int

                behavior countIt : (xs: List<Int>) -> Count
                    ensures List.all(x -> x >= 0, xs) && value.value >= 0
                """);

        assertEquals(Set.of("List.foldFrom"), required(db, "inrule"));
        assertEquals(Set.of(), predicted(db, "inrule"),
                "the walk that listed where a module writes expressions did not list `ensures`");
    }
}
