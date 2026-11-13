package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.UUID;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A statement whose every part holds the statement before it twice is one object held in two
 * places, and the ways down a chain of them are two to its length. What a statement says of itself
 * that is the same wherever it stands is said once ({@link SharedPropositions#fact}), so a reader
 * asking it is asking each statement once and not every way down to its parts.
 *
 * <p>Counted in the statements the work is done for and not timed: a spelling a String holds
 * bounds how long a chain can be made, and the ways down a chain that long are fewer than a clock
 * tells from the statements.
 */
class WhatAStatementSaysOfItselfIsAskedOfItOnceHoweverManyPartsHoldItTest {

    private static final int LENGTH = 20;

    /** Each statement is a conjunction of the one before it and a disjunction of that and a truth
     *  of its own; the truths are this test's own, so no other test has asked of them. */
    private static Proposition chainOf(int length) {
        String mine = UUID.randomUUID().toString();
        Proposition held = CompoundSamples.truth(mine + "0");
        for (int at = 1; at <= length; at++) {
            held = Proposition.all(List.of(held,
                    Proposition.any(List.of(held, CompoundSamples.truth(mine + at)))));
        }
        return held;
    }

    /** What goes down the parts as a reader of the parts does, asking each part of its owner. */
    private static boolean someAnswers(Proposition stated, int[] worked) {
        return SharedPropositions.fact(stated, SharedPropositions.Fact.ANSWERING, each -> {
            worked[0]++;
            return each.partsHeld().stream().anyMatch(part -> someAnswers(part, worked));
        });
    }

    @Test
    void aChainOfStatementsHoldingTheOneBeforeTwiceIsWorkedOutOnceForEachStatement() {
        Proposition chain = chainOf(LENGTH);
        int[] worked = {0};

        assertFalse(someAnswers(chain, worked));

        // Each level is a conjunction, a disjunction and a truth, and the first is a truth.
        assertEquals(3 * LENGTH + 1, worked[0]);
    }

    @Test
    void aStatementAskedAgainIsNotWorkedOutAgain() {
        Proposition chain = chainOf(LENGTH);
        int[] worked = {0};
        someAnswers(chain, worked);
        int once = worked[0];

        someAnswers(chain, worked);

        assertEquals(once, worked[0]);
    }

    @Test
    void whatReadersAskOfAChainIsAnsweredWithoutGoingDownEveryWayToItsParts() {
        Proposition chain = chainOf(LENGTH);

        assertFalse(Proposition.leavesSomethingUnread(chain));
        assertTrue(Proposition.stopsIn(chain).isEmpty());
        assertFalse(Proposition.saysASearchReachesBelow(chain));
        assertFalse(Proposition.aboutAnAnswer(chain));
    }
}
