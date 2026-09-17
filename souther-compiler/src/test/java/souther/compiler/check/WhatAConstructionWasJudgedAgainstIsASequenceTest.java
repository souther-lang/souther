package souther.compiler.check;

import souther.compiler.check.InvariantChecker.ClauseJudgments;
import souther.compiler.check.InvariantChecker.Judged;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * What a construction was judged against is a sequence, and is compared as one.
 *
 * <p>Held because it is now part of an answer. A report names these clauses in the order they were
 * declared and labels their places in it, so the order is something this says; the answer holding it
 * is kept or discarded by what {@code equals} says, and an answer kept for being what it was while
 * what it says has changed is a report that goes on saying the old thing. Said as a map keyed by the
 * clause, that is exactly what would happen — {@code Map.equals} is about entries.
 *
 * <p>Both directions. That two orders are told apart is the half that was missing; that the same
 * order compares equal is the half that makes it an answer worth keeping at all, since an answer
 * that never equals its predecessor stops every cut below it.
 */
class WhatAConstructionWasJudgedAgainstIsASequenceTest {

    private static final TypeKey DECLARED = new TypeKey("shop.prices", "Amount");

    @Test
    void theSameClausesInAnotherOrderAreNotTheSameJudgment() {
        assertNotEquals(judged(0, 1), judged(1, 0),
                "a report names these in the order they are held in, so two orders are two reports");
    }

    @Test
    void andTheSameClausesInTheSameOrderAre() {
        assertEquals(judged(0, 1), judged(0, 1),
                "nothing about this construction changed, so nothing that read it has to run again");
        assertEquals(judged(0, 1).hashCode(), judged(0, 1).hashCode(),
                "and it can be looked up by what it is");
    }

    /**
     * One clause, judged twice. There is no answer to which of the two a report is about, so there
     * is no such value — what a clause reached twice comes to is joined where it is recorded.
     */
    @Test
    void oneClauseIsJudgedOnce() {
        List<Judged> twice = new ArrayList<>();
        twice.add(unsettled(0));
        twice.add(unsettled(0));

        assertThrows(Clause.NotOneClause.class, () -> new ClauseJudgments(twice));
    }

    private static ClauseJudgments judged(int... ordinals) {
        List<Judged> read = new ArrayList<>();
        for (int ordinal : ordinals) {
            read.add(unsettled(ordinal));
        }
        return new ClauseJudgments(read);
    }

    private static Judged unsettled(int ordinal) {
        return new Judged(new Clause.Ref(
                new Clause.Id(TypeSymbols.declared(DECLARED), ordinal), java.util.Optional.empty()),
                ClauseStatus.UNKNOWN);
    }
}
