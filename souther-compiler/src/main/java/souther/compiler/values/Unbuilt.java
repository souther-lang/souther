package souther.compiler.values;

import java.util.ArrayList;
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

    /**
     * A shortfall a rule of the model is answerable for, and which written thing it is about.
     *
     * <p>The occurrence and not the position. An allowance is held per position and every rule
     * reaching one pays into it, so which of them asked for the machine that was refused is not a
     * thing the position knows — recovered from there, this became a fact about every rule that
     * mentions the place.
     *
     * @param at what was being worked out when it was refused, which is what the reason is about
     * @param occurrence what asked, which is what a reader is sent to
     * @param why what a rule is answerable for, which is what {@link UnreadReason.About#A_RULE}
     *            says of it
     */
    public record RuleShortfall<A>(A at, AuthoredOccurrence occurrence, UnreadReason why) {

        public RuleShortfall {
            if (at == null || occurrence == null || why == null) {
                throw new IllegalArgumentException("a shortfall about a rule says where, what asked"
                        + " and what it was");
            }
            if (why.about() != UnreadReason.About.A_RULE) {
                throw new IllegalArgumentException(
                        "a reason about " + why.about() + " names no rule to be about: " + why);
            }
        }
    }

    /**
     * A shortfall no rule is answerable for, which names none.
     *
     * <p>No occurrence, and that is what it says rather than something missing from it. What ran out
     * is the allowance for what the rules of the position come to between them; the same rules met
     * in another order would have been built, so there is nothing anybody wrote for this to be
     * about.
     */
    public record AnswerShortfall<A>(A at, UnreadReason why) {

        public AnswerShortfall {
            if (at == null || why == null) {
                throw new IllegalArgumentException("a shortfall about an answer says where and what"
                        + " it was");
            }
            if (why.about() != UnreadReason.About.THE_ANSWER) {
                throw new IllegalArgumentException(
                        "a reason about " + why.about() + " is not one the answer is short of: "
                                + why);
            }
        }
    }

    private final List<RuleShortfall<A>> aboutARule = new ArrayList<>();
    private final List<AnswerShortfall<A>> aboutTheAnswer = new ArrayList<>();

    /** Records what {@code made} says about {@code atom}, where it says the answer was not built. */
    void note(A atom, Realization made) {
        switch (made) {
            case Realization.Exact _ -> { }
            case Realization.OverTheMachineLimit it -> add(new RuleShortfall<>(atom,
                    it.occurrence(), UnreadReason.PATTERN_TOO_COSTLY));
            case Realization.OverTheAnswerLimit _ -> add(new AnswerShortfall<>(atom,
                    UnreadReason.EXACT_VALUES_TOO_COSTLY));
        }
    }

    private void add(RuleShortfall<A> one) {
        if (!aboutARule.contains(one)) {
            aboutARule.add(one);
        }
    }

    private void add(AnswerShortfall<A> one) {
        if (!aboutTheAnswer.contains(one)) {
            aboutTheAnswer.add(one);
        }
    }

    boolean isEmpty() {
        return aboutARule.isEmpty() && aboutTheAnswer.isEmpty();
    }

    /** The positions, for a reader that needs to know which of them widened. */
    Set<A> names() {
        Set<A> out = new LinkedHashSet<>();
        aboutARule.forEach(each -> out.add(each.at()));
        aboutTheAnswer.forEach(each -> out.add(each.at()));
        return Collections.unmodifiableSet(out);
    }

    /** What a rule of the model is answerable for, each saying which written thing asked. */
    List<RuleShortfall<A>> aboutARule() {
        return List.copyOf(aboutARule);
    }

    /** What the answer is answerable for, which names no rule. */
    List<AnswerShortfall<A>> aboutTheAnswer() {
        return List.copyOf(aboutTheAnswer);
    }

    /**
     * The same reasons, put beside the ones a reading already had at each position.
     *
     * <p>What a position was left holding, which is a reader's question about the place rather than
     * about who asked. The occurrence is left out here and kept where the shortfall is: a position
     * says how wide it is and why, and which written thing paid for that is a different question
     * with a different reader.
     */
    Map<A, List<UnreadReason>> beside(Map<A, List<UnreadReason>> standing) {
        if (isEmpty()) {
            return standing;
        }
        Map<A, List<UnreadReason>> out = new LinkedHashMap<>(standing);
        aboutARule.forEach(each -> put(out, each.at(), each.why()));
        aboutTheAnswer.forEach(each -> put(out, each.at(), each.why()));
        return out;
    }

    private void put(Map<A, List<UnreadReason>> out, A atom, UnreadReason why) {
        List<UnreadReason> all = new ArrayList<>(out.getOrDefault(atom, List.of()));
        if (!all.contains(why)) {
            all.add(why);
        }
        out.put(atom, all);
    }
}
