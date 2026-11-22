package souther.compiler.partition;

import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.CopyOnWriteArrayList;
import java.util.function.Predicate;

/**
 * Answers kept by what was asked for, each with what working it out asked of someone else and
 * was answered: an answer is taken again only by an asker who is answered the same.
 *
 * <p>For work that turns on its question and, beside it, on yes-or-no answers it asks for along
 * the way, where who gives those answers differs from one asking to the next. Kept by the question
 * alone, an answer worked out under one set of them would be handed to an asker given another;
 * not kept at all, the work is done again for every asker though most are answered alike. So what
 * was asked is written down with the answer, and asked again of whoever wants it next, which is
 * as many questions as the work asked and none of the work.
 *
 * <p>What was asked is told apart by which object it is, as the work asked it of that one. Asked
 * from several threads.
 *
 * @param <K> what an answer is asked for
 * @param <Q> what the work asks about on the way
 * @param <V> the answer
 */
final class KeptByWhatItAsked<K, Q, V> {

    private record Kept<Q, V>(Map<Q, Boolean> answered, V answer) {}

    private final Map<K, List<Kept<Q, V>>> kept = new ConcurrentHashMap<>();

    /**
     * The answer kept for {@code asked} that was worked out under the answers {@code answers}
     * gives, or null where none was.
     */
    V of(K asked, Predicate<Q> answers) {
        for (Kept<Q, V> each : kept.getOrDefault(asked, List.of())) {
            boolean same = true;
            for (Map.Entry<Q, Boolean> one : each.answered().entrySet()) {
                same &= answers.test(one.getKey()) == one.getValue();
            }
            if (same) {
                return each.answer();
            }
        }
        return null;
    }

    /**
     * That working {@code asked} out came to {@code answer}, having asked about each key of
     * {@code answered} and been given its value, and about nothing else.
     */
    void keep(K asked, Map<Q, Boolean> answered, V answer) {
        kept.computeIfAbsent(asked, _ -> new CopyOnWriteArrayList<>())
                .add(new Kept<>(answered, answer));
    }
}
