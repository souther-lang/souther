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
 * entirely on which of the two happened.
 *
 * <p><b>And the two are kept apart, because they are owed to different people.</b> A pattern larger
 * than any machine this holds is a rule somebody wrote and can write differently, so a report may
 * name the rule. An allowance run down by everything the position admits is about no rule at all:
 * the same rules in another order would have been built, and naming the one that happened to be
 * last sends an author to change something that is not why. Kept in one bag, whoever filed the bag
 * under a rule filed both.
 *
 * <p>More than one where more than one happened. A position reached by several rules can have a
 * pattern this would not build and, having widened there, an answer it would not build either.
 */
public final class Unbuilt<A> {

    private final Map<A, Set<UnreadReason>> aboutARule = new LinkedHashMap<>();
    private final Map<A, Set<UnreadReason>> aboutTheAnswer = new LinkedHashMap<>();

    /** Records what {@code made} says about {@code atom}, where it says the answer was not built. */
    void note(A atom, Realization made) {
        switch (made) {
            case Realization.Exact _ -> { }
            case Realization.OverTheMachineLimit _ ->
                    add(aboutARule, atom, UnreadReason.PATTERN_TOO_COSTLY);
            case Realization.OverTheAnswerLimit _ ->
                    add(aboutTheAnswer, atom, UnreadReason.EXACT_VALUES_TOO_COSTLY);
        }
    }

    private void add(Map<A, Set<UnreadReason>> to, A atom, UnreadReason reason) {
        to.computeIfAbsent(atom, _ -> new LinkedHashSet<>()).add(reason);
    }

    boolean isEmpty() {
        return aboutARule.isEmpty() && aboutTheAnswer.isEmpty();
    }

    /** The positions, for a reader that needs to know which of them widened. */
    Set<A> names() {
        Set<A> out = new LinkedHashSet<>(aboutARule.keySet());
        out.addAll(aboutTheAnswer.keySet());
        return Collections.unmodifiableSet(out);
    }

    /** What a rule of the model is answerable for, which a report may name the rule of. */
    Map<A, List<UnreadReason>> aboutARule() {
        return listed(aboutARule);
    }

    /** What the answer is answerable for, which names no rule. */
    Map<A, List<UnreadReason>> aboutTheAnswer() {
        return listed(aboutTheAnswer);
    }

    private Map<A, List<UnreadReason>> listed(Map<A, Set<UnreadReason>> of) {
        Map<A, List<UnreadReason>> out = new LinkedHashMap<>();
        of.forEach((atom, why) -> out.put(atom, List.copyOf(why)));
        return Collections.unmodifiableMap(out);
    }

    /** The same reasons, put beside the ones a reading already had at each position. */
    Map<A, List<UnreadReason>> beside(Map<A, List<UnreadReason>> standing) {
        if (isEmpty()) {
            return standing;
        }
        Map<A, List<UnreadReason>> out = new LinkedHashMap<>(standing);
        put(out, aboutARule);
        put(out, aboutTheAnswer);
        return out;
    }

    private void put(Map<A, List<UnreadReason>> out, Map<A, Set<UnreadReason>> mine) {
        mine.forEach((atom, why) -> {
            List<UnreadReason> all = new java.util.ArrayList<>(out.getOrDefault(atom, List.of()));
            why.forEach(each -> {
                if (!all.contains(each)) {
                    all.add(each);
                }
            });
            out.put(atom, all);
        });
    }
}
