package souther.compiler.collect;

import java.util.LinkedHashMap;
import java.util.Map;
import java.util.function.Function;

/**
 * The answers to the questions asked most lately, as many as it was made to keep, so an answer
 * asked for again while it is kept is not worked out again.
 *
 * <p>For a memo of a function of its question alone whose answers are large and asked again soon
 * or not for a long while: a walk that puts the same few questions to every step of a long run of
 * steps. A table that keeps every answer keeps all of them for as long as it is held, though each
 * was asked only around the steps that put it; this keeps the ones asked last and lets the one
 * asked longest ago go, as a cache that replaces its least recently used line does. An answer it no
 * longer holds is only worked out again, and since it is a function of the question, worked out
 * again it is the answer it was.
 *
 * <p>Least recently used rather than a slot per hash ({@link RecentAnswers}), because these answers
 * are dear to work out: two questions asked side by side never push each other out while fewer
 * than it keeps are in use.
 *
 * <p>Asked from any thread. The table is held only to look an answer up and to put one in; an
 * answer is worked out outside it, so working one out may ask this memo for another, and two
 * threads that met at one question may both work it out and either answer be the one kept.
 *
 * @param <Q> the question, immutable and equal by what it asks
 * @param <A> the answer, never null
 */
public final class LatelyAsked<Q, A> {

    private final int keeps;
    private final LinkedHashMap<Q, A> answers;

    /** Keeping the answers to the {@code keeps} questions asked most lately. */
    public LatelyAsked(int keeps) {
        if (keeps < 1) {
            throw new IllegalArgumentException("a memo keeps some answer, not " + keeps);
        }
        this.keeps = keeps;
        this.answers = new LinkedHashMap<>(16, 0.75f, true);
    }

    /** The answer to {@code question}: the one kept, or {@code working} applied to it, kept from
     *  now on. */
    public A answer(Q question, Function<? super Q, ? extends A> working) {
        synchronized (answers) {
            A had = answers.get(question);
            if (had != null) {
                return had;
            }
        }
        A answer = working.apply(question);
        if (answer == null) {
            throw new IllegalArgumentException("a memo keeps answers, and " + question
                    + " was answered with none");
        }
        synchronized (answers) {
            A raced = answers.putIfAbsent(question, answer);
            if (raced != null) {
                return raced;
            }
            if (answers.size() > keeps) {
                Map.Entry<Q, A> eldest = answers.entrySet().iterator().next();
                answers.remove(eldest.getKey());
            }
        }
        return answer;
    }
}
