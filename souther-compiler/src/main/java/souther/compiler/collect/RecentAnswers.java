package souther.compiler.collect;

import java.util.function.Function;

/**
 * The answers to a question asked last, each kept in the slot its question's hash falls in, so an
 * answer asked for again while it is kept is not worked out again.
 *
 * <p>For a memo of a function of its question alone, asked by a search that makes a new question at
 * every step. A table that keeps every answer keeps one per step of every path the search took, and
 * grows for as long as the search runs; this keeps as many as it has slots, the newest in each, as a
 * direct-mapped cache keeps a line. An answer it no longer holds is only worked out again, and since
 * it is a function of the question, worked out again it is the answer it was.
 *
 * <p>Written and read without a lock. A slot holds a question with its answer as one immutable
 * pair, so a reader finds a question with the answer that was worked out for it; two threads filling
 * one slot leave one of their pairs in it.
 *
 * @param <Q> the question, immutable and equal by what it asks
 * @param <A> the answer
 */
public final class RecentAnswers<Q, A> {

    /** A question with its answer. */
    private record Answered<Q, A>(Q question, A answer) {}

    private final Object[] slots;

    /** As many slots as two to {@code bits}. */
    public RecentAnswers(int bits) {
        if (bits < 1 || bits > 24) {
            throw new IllegalArgumentException("a table of two to " + bits + " slots");
        }
        this.slots = new Object[1 << bits];
    }

    /** The answer to {@code question}: the one kept, or {@code working} applied to it, kept from
     *  now on. */
    @SuppressWarnings("unchecked")
    public A answer(Q question, Function<? super Q, ? extends A> working) {
        int hash = question.hashCode();
        int slot = (hash ^ (hash >>> 16)) & (slots.length - 1);
        if (slots[slot] instanceof Answered<?, ?> there && there.question().equals(question)) {
            return (A) there.answer();
        }
        A answer = working.apply(question);
        slots[slot] = new Answered<>(question, answer);
        return answer;
    }
}
