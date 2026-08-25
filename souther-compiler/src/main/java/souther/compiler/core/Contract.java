package souther.compiler.core;

import souther.compiler.types.BindingId;
import souther.compiler.types.ResolvedCase;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Optional;

/**
 * What a behavior declares about the relation between what it is given and what it answers, as it
 * runs.
 *
 * <p>The executable reading of a declaration and not the declaration. The language reads an
 * {@code ensures} two ways — this one, with the operations it is made of inlined, and the one the
 * analysis reads with them left standing ({@code check.StatedContract}) — and what is here is the
 * first. A reader wanting to reason about what the author wrote wants the other one; a reader that
 * has to decide whether an answer keeps the declaration wants this.
 *
 * <p>Already specialized. There is one rule per case an arm names, because {@code value} is read as
 * what that case holds and the cases hold different things, so a reader does not specialize again.
 * Every rule whose guard holds is a rule the answer is held to: a declaration states a conjunction,
 * not an ordered choice, and one answer may satisfy several guards — a data may be a case of two
 * sums its module declares.
 *
 * <p>Where a rule was written is not here. A violation is reported by the clause, so the clause's
 * name travels with the rule; the position, the arm and the ordinals the module numbered its terms
 * with belong to the declaration as the author holds it ({@code check.BehaviorContract}), and a
 * reader that had them would have a value an unrelated edit moves.
 */
public record Contract(ValueName.Behavior behavior, List<Param> params, Type output,
                       List<Rule> rules) {

    public Contract {
        params = List.copyOf(params);
        rules = List.copyOf(rules);
    }

    /**
     * A parameter as a rule names it: where it is bound, what the author calls it, and what it
     * holds.
     *
     * <p>A rule names it by its binding and never by the spelling. The spelling is carried for a
     * reader showing what a behavior states, which is why it is here rather than looked up on the
     * declaration by whoever needs to show one.
     *
     * <p>Which one it is, is where it stands in {@link Contract#params()}. That is the order the
     * signature takes them in; a number beside it would be the same fact twice, and whether an
     * argument arrives in that position at all is the calling convention of whoever emits the
     * check.
     */
    public record Param(BindingId binding, String name, Type type) {}

    /**
     * One statement: when it applies, what {@code value} is where it does, and what has to hold.
     *
     * @param condition the checker's elaboration of what the author wrote — what runs
     * @param readsAnswer whether the rule as it is written refers to the answer through
     *     {@code value}. Decided by the checker off the written rule and carried, rather than read
     *     back off {@code condition}: what a rule reads is what the declaration says
     *     (spec §example-ensures, §ensures-discharge-capability), and derived from the elaboration
     *     it would move the day the elaboration began folding a term away — an {@code example} row
     *     writing a bare case name would then be held to a different set of rules because the
     *     compiler had got better at simplifying.
     * @param clause the name a violation of this is reported under, where the author named it
     */
    public record Rule(Guard guard, BindingId value, Core condition, boolean readsAnswer,
                       Optional<String> clause) {

        public Rule {
            if (condition == null) {
                throw new IllegalArgumentException("a rule is something that has to hold");
            }
        }

        /** What {@code value} is read as here: what the case holds, or the whole answer where the
         *  rule applies to every answer. */
        public Type valueType(Type output) {
            return guard instanceof Guard.Case c ? c.selected().bound() : output;
        }
    }

    /** When a rule applies. */
    public sealed interface Guard {

        /** The rule applies to every answer: the form written where the answer has no cases. */
        record Always() implements Guard {}

        /**
         * The rule applies where the answer is this case.
         *
         * <p>The case as this compile resolved it and not the selector alone: a reader deciding
         * whether one rule's case is inside another's is asking about what each covers, and going
         * back to the declarations for that is a second reading.
         */
        record Case(ResolvedCase selected) implements Guard {}
    }
}
