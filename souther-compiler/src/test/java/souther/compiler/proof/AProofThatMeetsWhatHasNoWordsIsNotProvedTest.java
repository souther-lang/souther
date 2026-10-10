package souther.compiler.proof;

import org.junit.jupiter.api.Test;

import souther.compiler.semantics.Unsayable;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A proof that stops on a value the domain has no words for has not proved its statement, and
 * says why: the statement is in words the domain has, and what lacked them is a value the proof
 * needed. It is no closing of the statement — a closing is only what {@link LibraryProver#closes}
 * shows.
 */
class AProofThatMeetsWhatHasNoWordsIsNotProvedTest {

    @Test
    void aReadingStoppedOnWhatHasNoWordsLeavesTheStatementOpen() {
        Unsayable why = Unsayable.HOW_MANY_TIMES_A_STRING_STANDS_INSIDE_ANOTHER;
        assertEquals(new LibraryProver.Outcome.Open(new Unproved.TurnsOnWhatIsNotSaid(why)),
                LibraryProver.stoppedAt(new Reading.Stopped(new Library.Settled.Unsaid(why))));
    }
}
