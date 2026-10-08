package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.coverage.ControlPlace;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.reach.Reachability;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a path takes in about a dependency's answer is known of that evaluation, however the
 * conditions on the way name it — and of no other evaluation.
 *
 * <p>A name given the answer is the call it was given, so {@code x < 5} taken in leaves nothing for
 * {@code x < 6} to fail on, and a name for that name is the same value again. Two calls are two
 * answers — a counter hands out a new number each time — so what the first came to says nothing
 * about the second. A name given arithmetic over the answer is that arithmetic and not the answer.
 */
class WhatAPathKnowsOfAnAnswerIsKnownOfThatEvaluationTest {

    private static final String MODEL = """
            module d

            data Free
            data Charged = { yen: Int }

            behavior nextId : () -> Int

            behavior charge : () -> Free | Charged
                depends on nextId
                constructs Charged

            let charge (nextId) = {
                BODY
                Charged { yen = 500 }
            }
            """;

    /** How many arms of {@code charge} are proven to be reached by nothing, written as
     *  {@code body}. */
    private static long provenIn(String body) {
        Compilation c = Compilation.ofSource(MODEL.replace("BODY", body), "d");
        Map<String, PathReachability.Answers> byBehavior =
                c.db().ask(new Adequacy.PathReached("d")).value();
        assertTrue(byBehavior != null && byBehavior.containsKey("charge"),
                "the module answers nothing about `charge`");
        return byBehavior.get("charge").found().entrySet().stream()
                .filter(each -> each.getKey() instanceof ControlPlace.Arm)
                .filter(each -> each.getValue() instanceof Reachability.Unreachable)
                .count();
    }

    @Test
    void aGuardOnTheNameOfAnAnswerIsKnownWhereverThatNameIsRead() {
        assertEquals(1, provenIn("""
                let x = nextId()
                    guard x < 5 else Free
                    guard x < 6 else Free"""),
                "below five, nothing departs at six");
        assertEquals(1, provenIn("""
                let x = nextId()
                    let y = x
                    guard x < 5 else Free
                    guard y < 6 else Free"""),
                "and a name for that name is the same answer");
    }

    @Test
    void twoCallsAreTwoAnswersAndArithmeticIsNotTheAnswer() {
        assertEquals(0, provenIn("""
                let x = nextId()
                    let y = nextId()
                    guard x < 5 else Free
                    guard y < 6 else Free"""),
                "the second call answers whatever it answers");
        assertEquals(0, provenIn("""
                let x = nextId()
                    let y = x + 1
                    guard x < 5 else Free
                    guard y < 5 else Free"""),
                "four is below five and one more than it is not");
    }
}
