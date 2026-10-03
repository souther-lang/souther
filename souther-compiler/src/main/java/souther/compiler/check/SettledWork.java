package souther.compiler.check;

/**
 * Work whose answer is settled by the value that describes it, and by nothing else.
 *
 * <p>What it may spend is minted inside {@link #workedOut} for it and for no other question, and
 * what it reads is what it holds. So the same work asked from two places in one revision comes to
 * the same answer, and a revision that has done it once lends the answer to every later asking
 * ({@link DeclarationReadings#settled}). A search that visits one position from many places is
 * otherwise doing the work once per visit.
 *
 * <p>Two of these are the same work where they are equal, so an implementation is a value: a record
 * of everything the answer is worked out from. A component left out is two pieces of work answered
 * alike, and a component compared by identity is the same work done twice.
 *
 * <p>Asks nothing of whoever keeps it. The answer is made while the keeper is filling its table, so
 * work that asked the keeper for other work would be asking it in the middle of that.
 *
 * @param <A> what the work comes to, never null: an empty answer is an answer and is kept like any
 *            other, since the work that cost the most is often the work that came to nothing
 */
public interface SettledWork<A> {

    /** The answer, worked out here and now. */
    A workedOut();

    /**
     * {@code work} done: the one place any of it is worked out, so whatever keeps the answers keeps
     * what this says.
     */
    static <A> A done(SettledWork<A> work) {
        SettledWorkDone.count(work.getClass());
        A answer = work.workedOut();
        if (answer == null) {
            throw new IllegalStateException("work comes to an answer, empty or not: " + work);
        }
        return answer;
    }

    /**
     * How many times work of {@code kind} has been worked out rather than lent, for a test holding
     * a reader to how often it asks.
     *
     * <p>What a caller is held to is that work asked from many places is done for the first of them
     * — a shape, and not a speed.
     */
    static long timesDone(Class<?> kind) {
        return SettledWorkDone.of(kind);
    }
}
