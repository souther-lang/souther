package souther.compiler.revision;

import org.junit.jupiter.api.Test;

import java.util.Optional;
import java.util.concurrent.atomic.AtomicLong;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Work a revision has done is lent for the rest of the revision and goes when it moves.
 *
 * <p>The answer is settled by the work, so the same work asked twice in one revision is done once;
 * and a table outliving the revision would hold every pattern and set an author wrote on the way to
 * the one they meant.
 */
class WhatARevisionKnowsIsWorkedOutOnceAndGoesWithItTest {

    /** Work whose answer is its word, or nothing where the word is empty. */
    private record Echo(String word) implements RevisionWork<Optional<String>> {

        @Override
        public Optional<String> workedOut(RevisionKnowledge revision) {
            return word.isEmpty() ? Optional.empty() : Optional.of(word);
        }
    }

    /** Work made of another piece of work, which it borrows rather than does. */
    private record Twice(String word) implements RevisionWork<String> {

        @Override
        public String workedOut(RevisionKnowledge revision) {
            String once = revision.settled(new Echo(word)).orElse("");
            return once + once;
        }
    }

    /** Work that borrows the work it was borrowed by, which comes round to itself. */
    private record Round(String side) implements RevisionWork<String> {

        @Override
        public String workedOut(RevisionKnowledge revision) {
            return revision.settled(new Round(side.equals("there") ? "back" : "there"));
        }
    }

    /** Work that fails on its own account, for what a failure leaves behind. */
    private record Failing(String word) implements RevisionWork<String> {

        @Override
        public String workedOut(RevisionKnowledge revision) {
            throw new IllegalArgumentException("it could not: " + word);
        }
    }

    /** Work that comes to no answer at all, which is not one of the answers work can come to. */
    private record Nothing() implements RevisionWork<String> {

        @Override
        public String workedOut(RevisionKnowledge revision) {
            return null;
        }
    }

    @Test
    void workAskedTwiceInOneRevisionIsDoneOnce() {
        RevisionKnowledge known = RevisionKnowledge.keptFor(() -> 1, StoreWork.UNWATCHED);

        long before = RevisionKnowledge.timesDone(Echo.class);
        assertEquals(Optional.of("a"), known.settled(new Echo("a")));
        assertEquals(Optional.of("a"), known.settled(new Echo("a")),
                "the second asking is answered with what the first came to");
        assertEquals(Optional.of("b"), known.settled(new Echo("b")),
                "and other work is other work");
        assertEquals(2, RevisionKnowledge.timesDone(Echo.class) - before);
    }

    @Test
    void anEmptyAnswerIsKeptLikeAnyOther() {
        RevisionKnowledge known = RevisionKnowledge.keptFor(() -> 1, StoreWork.UNWATCHED);

        long before = RevisionKnowledge.timesDone(Echo.class);
        assertEquals(Optional.empty(), known.settled(new Echo("")));
        assertEquals(Optional.empty(), known.settled(new Echo("")));
        assertEquals(1, RevisionKnowledge.timesDone(Echo.class) - before,
                "work that came to nothing is not done again for asking again");
    }

    /**
     * Work borrowed by other work is the producer's, done once however many borrowers ask, and the
     * borrower asking it while it is being done is not refused.
     */
    @Test
    void workBorrowedWhileOtherWorkIsDoneIsDoneOnceForEveryBorrower() {
        RevisionKnowledge known = RevisionKnowledge.keptFor(() -> 1, StoreWork.UNWATCHED);

        long echoes = RevisionKnowledge.timesDone(Echo.class);
        long twices = RevisionKnowledge.timesDone(Twice.class);
        assertEquals("cc", known.settled(new Twice("c")));
        assertEquals(Optional.of("c"), known.settled(new Echo("c")),
                "what the borrower borrowed is what the revision knows");
        assertEquals("cc", known.settled(new Twice("c")));

        assertEquals(1, RevisionKnowledge.timesDone(Echo.class) - echoes,
                "the borrowed work was done for the borrower and lent to the asking after it");
        assertEquals(1, RevisionKnowledge.timesDone(Twice.class) - twices);
    }

    @Test
    void whatWasDoneUnderOneRevisionIsDoneAgainUnderTheNext() {
        AtomicLong revision = new AtomicLong(1);
        RevisionKnowledge known = RevisionKnowledge.keptFor(revision::get, StoreWork.UNWATCHED);
        known.settled(new Echo("a"));

        revision.incrementAndGet();
        long before = RevisionKnowledge.timesDone(Echo.class);
        known.settled(new Echo("a"));

        assertEquals(1, RevisionKnowledge.timesDone(Echo.class) - before,
                "not carried into a world it was not worked out in");
    }

    /** And knowledge with no revision behind it does the work at every asking. */
    @Test
    void withNoRevisionTheWorkIsDoneAtEveryAsking() {
        long before = RevisionKnowledge.timesDone(Echo.class);
        RevisionKnowledge.NONE.settled(new Echo("a"));
        RevisionKnowledge.NONE.settled(new Echo("a"));

        assertEquals(2, RevisionKnowledge.timesDone(Echo.class) - before);
    }

    /**
     * Work that borrows itself, through another, is refused at the second entry and the way round
     * is named — whether or not anything is kept.
     */
    @Test
    void workThatComesRoundToItselfIsRefusedWithTheWayRound() {
        for (RevisionKnowledge known : new RevisionKnowledge[] {
                RevisionKnowledge.keptFor(() -> 1, StoreWork.UNWATCHED), RevisionKnowledge.NONE}) {
            IllegalStateException refused = assertThrows(IllegalStateException.class,
                    () -> known.settled(new Round("back")));
            assertEquals("revision work borrows itself: Round[side=back] -> Round[side=there]"
                            + " -> Round[side=back]", refused.getMessage(),
                    "refused rather than done again until the stack ran out");
        }
    }

    /** And work that failed leaves nothing under way behind it, so asking again is not a cycle. */
    @Test
    void workThatFailedIsNotLeftUnderWay() {
        RevisionKnowledge known = RevisionKnowledge.keptFor(() -> 1, StoreWork.UNWATCHED);

        assertThrows(IllegalArgumentException.class, () -> known.settled(new Failing("x")));
        assertThrows(IllegalArgumentException.class, () -> known.settled(new Failing("x")),
                "the second asking fails on its own account and not as work borrowing itself");
    }

    /** The same work done for two revisions at once is two pieces of work and not a cycle. */
    @Test
    void theSameWorkForAnotherRevisionIsNotACycle() {
        RevisionKnowledge other = RevisionKnowledge.keptFor(() -> 2, StoreWork.UNWATCHED);

        assertEquals("done in the other",
                RevisionKnowledge.keptFor(() -> 1, StoreWork.UNWATCHED).settled(new Across(other)),
                "asked of the other revision while being done for this one, which is not the same"
                        + " piece of work");
    }

    /** Work that, done anywhere but in {@code other}, asks {@code other} for itself. */
    private record Across(RevisionKnowledge other) implements RevisionWork<String> {

        @Override
        public String workedOut(RevisionKnowledge revision) {
            return revision == other ? "done in the other" : other.settled(this);
        }
    }

    @Test
    void workThatComesToNoAnswerIsRefused() {
        assertThrows(IllegalStateException.class,
                () -> RevisionKnowledge.keptFor(() -> 1, StoreWork.UNWATCHED).settled(new Nothing()),
                "kept as a missing entry, it would be done again at every asking");
    }
}
