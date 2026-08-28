package souther.compiler.values;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The positions whose answer was not built while one reading was worked out, and why each of them
 * was not.
 *
 * <p>Names alone would be the widening without the reason. Every position here is left holding every
 * value, which is true and is short of what its rules say — and what an author does about it depends
 * entirely on which of the two happened. A pattern larger than any machine this holds is one they
 * wrote and can write differently; an allowance run down by everything the position admits is not
 * about a rule at all, and telling them to rewrite the one that was being built when it ran out
 * sends them to change something that is not why.
 *
 * <p>More than one where more than one happened. A position reached by several rules can have a
 * pattern this would not build and, having widened there, an answer it would not build either.
 */
final class Unbuilt<A> {

    private final Map<A, Set<UnreadReason>> why = new LinkedHashMap<>();

    /** Records what {@code made} says about {@code atom}, where it says the answer was not built. */
    void note(A atom, Realization made) {
        switch (made) {
            case Realization.Exact _ -> { }
            case Realization.OverTheMachineLimit _ ->
                    add(atom, UnreadReason.PATTERN_TOO_COSTLY);
            case Realization.OverTheAnswerLimit _ ->
                    add(atom, UnreadReason.EXACT_VALUES_TOO_COSTLY);
        }
    }

    private void add(A atom, UnreadReason reason) {
        why.computeIfAbsent(atom, _ -> new LinkedHashSet<>()).add(reason);
    }

    boolean isEmpty() {
        return why.isEmpty();
    }

    /** The positions, for a reader that needs to know which of them widened. */
    Set<A> names() {
        return Collections.unmodifiableSet(why.keySet());
    }

    /** The same reasons, put beside the ones a reading already had at each position. */
    Map<A, List<UnreadReason>> beside(Map<A, List<UnreadReason>> standing) {
        if (why.isEmpty()) {
            return standing;
        }
        Map<A, List<UnreadReason>> out = new LinkedHashMap<>(standing);
        why.forEach((atom, mine) -> {
            List<UnreadReason> all = new java.util.ArrayList<>(out.getOrDefault(atom, List.of()));
            mine.forEach(each -> {
                if (!all.contains(each)) {
                    all.add(each);
                }
            });
            out.put(atom, all);
        });
        return out;
    }
}
