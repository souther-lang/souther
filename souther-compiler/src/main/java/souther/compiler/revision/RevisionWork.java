package souther.compiler.revision;

/**
 * Work whose answer is settled by the value that describes it and by the allowance the work mints
 * for itself, and by nothing else.
 *
 * <p>So the same work asked from two places in one revision comes to the same answer, and a
 * revision that has done it once lends the answer to every later asking
 * ({@link RevisionKnowledge#settled}). A search visiting one position from many places, and a
 * reading meeting one set under many declarations, would otherwise do the work once per visit.
 *
 * <p><b>Who pays for what.</b> The work pays for what it builds and for nothing it borrows. An
 * answer another piece of work already made is an artifact that exists, and taking it is not
 * building it again: what the borrower's own allowance is spent on is only what it makes on top.
 * So a piece of work that borrows does it through the knowledge it is handed rather than by doing
 * the borrowed work itself, and the producer's cost is charged once, to the producer.
 *
 * <p><b>What work borrows never comes round to it.</b> A piece of work that borrows itself,
 * through however many others, has no answer to be kept: it would be done again inside itself for
 * as long as there was stack. So the borrowing is a graph with no cycle, and a piece of work asked
 * for while it is being done is refused with the way round it named
 * ({@link RevisionKnowledge#done}).
 *
 * <p>Two of these are the same work where they are equal, so an implementation is a value: a record
 * of everything the answer is worked out from. A component left out is two pieces of work answered
 * alike, and a component compared by identity is the same work done twice.
 *
 * @param <A> what the work comes to, never null: an empty answer is an answer and is kept like any
 *            other, since the work that cost the most is often the work that came to nothing
 */
public interface RevisionWork<A> {

    /** The answer, worked out here and now, borrowing whatever other work it needs from
     *  {@code revision}. */
    A workedOut(RevisionKnowledge revision);
}
