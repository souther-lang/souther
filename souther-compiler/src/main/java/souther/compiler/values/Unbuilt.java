package souther.compiler.values;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
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
     * <p>The pattern and not a rule. A machine is the pattern's, and the same pattern written into
     * three rules is one machine that all three asked for — so what is named here is what was
     * refused, and which rules are answerable for it is which of them asked for that pattern. Named
     * with one rule, two rules writing one pattern would have one of them answering for both.
     *
     * @param at what was being worked out when it was refused, which is what the reason is about
     * @param asked the pattern whose machine was refused, which is what a rule is answerable for
     *              having written
     * @param why what a rule is answerable for, which is what {@link UnreadReason.About#A_RULE}
     *            says of it
     */
    public record RuleShortfall<A>(A at, souther.compiler.regex.PatternPlan asked,
                                   UnreadReason why) {

        public RuleShortfall {
            if (at == null || asked == null || why == null) {
                throw new IllegalArgumentException("a shortfall about a rule says where, what was"
                        + " asked for and what it was");
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

    private final Set<RuleShortfall<A>> aboutARule = new LinkedHashSet<>();
    private final List<AnswerShortfall<A>> aboutTheAnswer = new ArrayList<>();
    /** The blocks whose answer was not built, which is the coordinate the machine was to be made
     *  in. Beside the shortfalls rather than read off them: those name the positions an author
     *  wrote, and several of those are one answer wherever a rule holds them as one value. */
    private final Set<Sameness.Block<A>> widened = new LinkedHashSet<>();

    /**
     * Records what {@code made} says about {@code block}, where it says the answer was not built.
     *
     * <p>Written down twice and about two things. What was not built is the block's one answer, so
     * that is what is short; what an author can act on is a rule they wrote at a position, so every
     * position of the block carries the reason. A block of one position is both of those at once,
     * which is what this was before any rule held two positions as one value.
     */
    void note(Sameness.Block<A> block, Realization made) {
        switch (made) {
            case Realization.Exact _ -> { }
            case Realization.OverTheMachineLimit it -> {
                widened.add(block);
                block.members().forEach(atom -> add(new RuleShortfall<>(atom,
                        it.asked(), UnreadReason.PATTERN_TOO_COSTLY)));
            }
            case Realization.OverTheAnswerLimit _ -> {
                widened.add(block);
                block.members().forEach(atom -> add(new AnswerShortfall<>(atom,
                        UnreadReason.EXACT_VALUES_TOO_COSTLY)));
            }
        }
    }

    private void add(RuleShortfall<A> one) {
        aboutARule.add(one);
    }

    private void add(AnswerShortfall<A> one) {
        if (!aboutTheAnswer.contains(one)) {
            aboutTheAnswer.add(one);
        }
    }

    boolean isEmpty() {
        return aboutARule.isEmpty() && aboutTheAnswer.isEmpty() && widened.isEmpty();
    }

    /** The blocks, for a reader that needs to know which answers widened. */
    Set<Sameness.Block<A>> names() {
        return Collections.unmodifiableSet(new LinkedHashSet<>(widened));
    }

    /**
     * What a rule of the model is answerable for, each saying which pattern was refused.
     *
     * <p>A set, because that is what these are. One pattern refused at one position is one fact
     * however many times the work met it, and nothing here is an order anybody may read: the order
     * somebody wrote their rules in is the reading's to say, and a set of facts joined from two
     * branches would say the order they were joined in.
     *
     * <p><b>Kept in the order they were recorded all the same.</b> Nothing may read the order, and
     * a compile has to come out the same twice — {@link Set#copyOf} iterates in an order salted per
     * run of the machine, so a downstream fold that seeds anything from these would put a report in
     * a different order on Tuesday.
     */
    Set<RuleShortfall<A>> aboutARule() {
        return Collections.unmodifiableSet(new LinkedHashSet<>(aboutARule));
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
    Standing<A> beside(Standing<A> standing) {
        Standing<A> out = standing;
        for (RuleShortfall<A> each : aboutARule) {
            out = out.alsoAt(Set.of(each.at()), each.why());
        }
        for (AnswerShortfall<A> each : aboutTheAnswer) {
            out = out.alsoAt(Set.of(each.at()), each.why());
        }
        return out;
    }
}
