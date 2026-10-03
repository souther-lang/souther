package souther.compiler.check;

import org.junit.jupiter.api.Test;

import java.util.Optional;
import java.util.concurrent.atomic.AtomicLong;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Work a revision has done is lent for the rest of the revision and goes when it moves.
 *
 * <p>Kept on the terms the extents are kept on ({@link LentReadings}): the answer is settled by the
 * work, so the same work asked twice in one revision is done once; and a table outliving the
 * revision would hold every pattern an author wrote on the way to the one they meant.
 */
class WhatARevisionKnowsOfSettledWorkGoesWhenTheRevisionMovesTest {

    /** Work whose answer is its word, or nothing where the word is empty. */
    private record Echo(String word) implements SettledWork<Optional<String>> {

        @Override
        public Optional<String> workedOut() {
            return word.isEmpty() ? Optional.empty() : Optional.of(word);
        }
    }

    /** Work that comes to no answer at all, which is not one of the answers work can come to. */
    private record Nothing() implements SettledWork<String> {

        @Override
        public String workedOut() {
            return null;
        }
    }

    @Test
    void workAskedTwiceInOneRevisionIsDoneOnce() {
        LentReadings lender = new LentReadings(DeclarationReadings.NONE, () -> 1,
                StoreWork.UNWATCHED);

        long before = SettledWork.timesDone(Echo.class);
        assertEquals(Optional.of("a"), lender.settled(new Echo("a")));
        assertEquals(Optional.of("a"), lender.settled(new Echo("a")),
                "the second asking is answered with what the first came to");
        assertEquals(Optional.of("b"), lender.settled(new Echo("b")),
                "and other work is other work");
        assertEquals(2, SettledWork.timesDone(Echo.class) - before);
    }

    @Test
    void anEmptyAnswerIsKeptLikeAnyOther() {
        LentReadings lender = new LentReadings(DeclarationReadings.NONE, () -> 1,
                StoreWork.UNWATCHED);

        long before = SettledWork.timesDone(Echo.class);
        assertEquals(Optional.empty(), lender.settled(new Echo("")));
        assertEquals(Optional.empty(), lender.settled(new Echo("")));
        assertEquals(1, SettledWork.timesDone(Echo.class) - before,
                "work that came to nothing is not done again for asking again");
    }

    @Test
    void whatWasDoneUnderOneRevisionIsDoneAgainUnderTheNext() {
        AtomicLong revision = new AtomicLong(1);
        LentReadings lender = new LentReadings(DeclarationReadings.NONE, revision::get,
                StoreWork.UNWATCHED);
        lender.settled(new Echo("a"));

        revision.incrementAndGet();
        long before = SettledWork.timesDone(Echo.class);
        lender.settled(new Echo("a"));

        assertEquals(1, SettledWork.timesDone(Echo.class) - before,
                "not carried into a world it was not worked out in");
    }

    /** And a reading with no revision behind it does the work at every asking. */
    @Test
    void withNoRevisionTheWorkIsDoneAtEveryAsking() {
        long before = SettledWork.timesDone(Echo.class);
        DeclarationReadings.NONE.settled(new Echo("a"));
        DeclarationReadings.NONE.settled(new Echo("a"));

        assertEquals(2, SettledWork.timesDone(Echo.class) - before);
    }

    @Test
    void workThatComesToNoAnswerIsRefused() {
        assertThrows(IllegalStateException.class, () -> SettledWork.done(new Nothing()),
                "kept as a missing entry, it would be done again at every asking");
    }
}
