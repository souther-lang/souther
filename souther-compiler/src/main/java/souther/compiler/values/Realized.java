package souther.compiler.values;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * A reading worked out, together with what could not be built while working it out.
 *
 * <p>Three facts settled by one piece of work and handed over together. Which values each position
 * admits is one; whether the reading admits anything at all is the second; and which limit stopped
 * this compiler where it stopped is the third. They are not separable questions — the second and
 * third are only answerable by doing the work the first needed — and a caller given the first alone
 * has to guess the others from what it holds. What it holds is a set widened to every value, and
 * every guess made from that is the wrong one: it reads a position nobody could work out as one the
 * rules left open.
 *
 * <p><b>The two shortfalls are apart because they are owed to different people.</b> What is about a
 * rule may be filed under that rule and shown to an author as something to change. What is about the
 * answer may not: the same rules in another order would have been built, so there is no rule to
 * name. A store that took either would be a store whose type says less than the model does.
 *
 * @param values what the reading leaves, every position it could not work out widened to every value
 * @param aboutARule what a rule of the model is answerable for, each saying which written thing
 *                   asked for what was refused. Not per position: an allowance is held per position
 *                   and every rule reaching one pays into it, so the place is what the spending was
 *                   arranged by and is not what any of it is about
 * @param aboutTheAnswer what the answer is answerable for, naming no rule and nothing written
 */
public record Realized<A>(AdmissibleValues<A> values,
                          List<Unbuilt.RuleShortfall<A>> aboutARule,
                          List<Unbuilt.AnswerShortfall<A>> aboutTheAnswer) {

    public Realized {
        aboutARule = List.copyOf(aboutARule);
        aboutTheAnswer = List.copyOf(aboutTheAnswer);
    }

    /**
     * Whether anything satisfies the reading.
     *
     * <p>Three answers, because a reading with a position nobody could work out has not been shown
     * to admit anything or to admit nothing. What stands there is every value, which is true and is
     * wider than the rules — so the reading may hold something the rules refuse, and reading it as
     * one that admits something is sound and is not exact.
     *
     * <p>Which is why the shortfall travels with it. A caller taking {@link Emptiness#UNDECIDED} for
     * "it admits something" and dropping what is here has claimed a reading is a branch anybody can
     * be in, and has kept no record of why nobody knows.
     */
    public Emptiness emptiness() {
        if (values.isBottom()) {
            return Emptiness.EMPTY;
        }
        return unbuilt().isEmpty() ? Emptiness.NONEMPTY : Emptiness.UNDECIDED;
    }

    /** Every position whose answer was not built, whichever of the two it is owed to. */
    public Set<A> unbuilt() {
        Set<A> out = new LinkedHashSet<>();
        aboutARule.forEach(each -> out.add(each.at()));
        aboutTheAnswer.forEach(each -> out.add(each.at()));
        return Collections.unmodifiableSet(out);
    }
}
