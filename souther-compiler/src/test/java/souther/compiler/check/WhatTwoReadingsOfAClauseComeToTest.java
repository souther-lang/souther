package souther.compiler.check;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The table two readings of one clause are combined by.
 *
 * <p>Held as a table rather than only through the programs that reach it, because what this is is an
 * abstract domain and what went wrong in it was not a program: the four values were once three on a
 * line, combined by taking the greater, which made "refused on every path" and "refused on some
 * path" one value. Nothing about that reads as wrong at a call site — a set called {@code refuted}
 * held clauses that were refuted — and the program that showed it needed two branches failing two
 * different clauses.
 *
 * <p>So the domain states what it means here, where the next change to it is read against the table
 * rather than against whichever construction happened to be in a test.
 */
class WhatTwoReadingsOfAClauseComeToTest {

    private static final ClauseStatus S = ClauseStatus.SETTLED;
    private static final ClauseStatus U = ClauseStatus.UNKNOWN;
    private static final ClauseStatus RS = ClauseStatus.REFUTED_SOMEWHERE;
    private static final ClauseStatus R = ClauseStatus.REFUTED;

    @Test
    void twoReadingsThatAgreeSayWhatTheyAgreedOn() {
        for (ClauseStatus one : ClauseStatus.values()) {
            assertEquals(one, ClauseStatus.of(one, one), one + " with itself");
        }
    }

    /** Established by one and refused by the other is established by neither, and refused by
     *  neither: which of them holds depends on the path, which is what {@code REFUTED_SOMEWHERE}
     *  says and what {@code REFUTED} may not. */
    @Test
    void aRefutationThatIsNotOnEveryPathIsNotARefutation() {
        assertEquals(RS, ClauseStatus.of(R, S));
        assertEquals(RS, ClauseStatus.of(R, U));
        assertEquals(RS, ClauseStatus.of(R, RS));
    }

    @Test
    void aReadingThatRefusedNothingLeavesNoRefutation() {
        assertEquals(U, ClauseStatus.of(S, U));
    }

    /** Once a path has been found that fails it, no other reading takes that back. */
    @Test
    void aClauseSomePathFailsGoesOnBeingOne() {
        assertEquals(RS, ClauseStatus.of(RS, S));
        assertEquals(RS, ClauseStatus.of(RS, U));
    }

    // --- the algebra, over the whole domain ------------------------------------------------------

    @Test
    void combiningIsCommutative() {
        for (ClauseStatus a : ClauseStatus.values()) {
            for (ClauseStatus b : ClauseStatus.values()) {
                assertEquals(ClauseStatus.of(a, b), ClauseStatus.of(b, a), a + " and " + b);
            }
        }
    }

    /** Which is what lets a construction under nested conditionals be folded a pair at a time. */
    @Test
    void combiningIsAssociative() {
        for (ClauseStatus a : ClauseStatus.values()) {
            for (ClauseStatus b : ClauseStatus.values()) {
                for (ClauseStatus c : ClauseStatus.values()) {
                    assertEquals(ClauseStatus.of(ClauseStatus.of(a, b), c),
                            ClauseStatus.of(a, ClauseStatus.of(b, c)),
                            a + ", " + b + ", " + c);
                }
            }
        }
    }

    // --- what each side is read for --------------------------------------------------------------

    /** E2011 asks this, and asks it of everything that is not established. */
    @Test
    void everythingButSettledIsAClauseTheGuardsDidNotEstablish() {
        assertFalse(S.unsettled());
        for (ClauseStatus one : List.of(U, RS, R)) {
            assertTrue(one.unsettled(), one.toString());
        }
    }

    /** E2010 asks this of what it points at where nothing is failed on every path. */
    @Test
    void aPathThatFailsItIsWhatRefusedSomewhereAnswers() {
        assertTrue(R.refusedSomewhere());
        assertTrue(RS.refusedSomewhere());
        assertFalse(U.refusedSomewhere());
        assertFalse(S.refusedSomewhere());
    }

    // --- a reading that did not read the clause ---------------------------------------------------

    /**
     * The same question against a reading that read nothing here. A refutation says the value fails
     * this clause where the reading that found it looked, and a reading that did not look is not
     * one it holds of.
     */
    @Test
    void aReadingThatSaysNothingTakesARefutationDownToOnePath() {
        assertEquals(RS, R.whereTheOtherReadingSaysNothing());
        assertEquals(RS, RS.whereTheOtherReadingSaysNothing());
        assertEquals(U, U.whereTheOtherReadingSaysNothing());
    }
}
