package souther.compiler.check;

import souther.compiler.types.SourceConstructOrigin;
import souther.compiler.types.WrittenOwner;

/**
 * Which rule of the model, and nothing about how anybody came to be holding it.
 *
 * <p>One answer per way a rule is written. An author writes a rule as a clause of a {@code data}'s
 * invariant, as a comparison in a body, as a predicate applied in a body, or as a clause of a
 * behavior's {@code ensures}; a question about coverage is raised by one of those, and what answers
 * it is a fact about that rule and not about the reading that reached it. So this is what a question
 * is filed under, and it is the same value however many times the rule is read.
 *
 * <p><b>A comparison and a predicate are two of them and not one "rule of a body".</b> They divide a
 * position differently — one places a line on an order and the other tells a set of values from the
 * rest — and a reader is shown a different construct for each. Held as one arm, the two would be
 * told apart by looking at what the rule turned out to do, which is the thing a key must not be
 * built out of.
 *
 * <p>Nothing here says where a rule was met. A guard inside a helper is read once per call of that
 * helper: the calls are different occurrences, they carry different comparison sites, and they are
 * one rule. Carrying the occurrence, two readings of one rule are two keys — the question would be
 * raised twice and answered twice, which is a reading raising a question rather than the model, and
 * is what a coverage obligation is written against. Where a rule was met is
 * {@link souther.compiler.partition.LineOrigin}'s, beside this rather than inside it.
 *
 * <p>Nothing here says what a rule <em>did</em>, either. Which side of a line the cut value falls
 * on, whether the comparison holds at it, which arms witness it, which declarations took an end in —
 * those are answers about a boundary, they are the same rule's whichever way they come out, and a
 * key holding them files one rule under several.
 */
public sealed interface RuleRef {

    /**
     * A clause of a {@code data}'s invariant.
     *
     * <p>The clause and not the declaration it is on. Two clauses of one declaration are two rules,
     * and a report owes a line to each ({@link Clause}).
     */
    record Invariant(Clause.Ref clause) implements RuleRef {

        public Invariant {
            if (clause == null) {
                throw new IllegalArgumentException("an invariant's rule is one of its clauses");
            }
        }
    }

    /**
     * A comparison a definition wrote, read for the answer of some behavior.
     *
     * <p>The comparison and not the fork testing it. A condition can be an application of a
     * function parameter, so one predicate handed to two calls is one rule and two predicates
     * written apart are two — neither of which the fork can say. Which fork this comparison was
     * read under is where it was met, and belongs beside this.
     *
     * <p><b>Read off the source and never off a measurement.</b> The two components are what the
     * author wrote: which behavior, and which construct of which module. A run's numbering of
     * comparisons is a fact about instrumentation — a condition both of whose arms can record
     * nothing is not numbered at all — and taking an identity from it says a rule exists because
     * something could be measured about it. A model states its rules whether or not this compiler
     * arranged to watch them.
     *
     * @param behavior whose body it is written in. Two behaviors calling one helper each read its
     *                 comparison, and the readings are what a coverage question is raised per
     * @param origin   which construct of which module the author wrote, which is what tells one
     *                 comparison from another wherever it is met
     */
    record Comparison(String behavior, SourceConstructOrigin origin)
            implements RuleRef {

        public Comparison {
            if (behavior == null || origin == null) {
                throw new IllegalArgumentException("a comparison of a body is one of some behavior's");
            }
            // Which definition wrote it is half of what tells this comparison from every other, and
            // it is held where the value is made rather than where one is published. A comparison of
            // a type's clause or of a behavior's `ensures` is answered for by the clause and the arm
            // it is in and never reaches here; one an analysis rebuilt was written by nobody.
            if (!(origin.owner() instanceof WrittenOwner.Body)) {
                throw new IllegalStateException("a comparison of a body was written by a"
                        + " definition, and this was written by " + origin.owner());
            }
        }

        /** The definition whose body wrote the comparison — not the behavior reading it, which a
         *  helper's comparison has one of per caller. */
        public WrittenOwner.Body writtenIn() {
            return (WrittenOwner.Body) origin.owner();
        }
    }

    /**
     * A predicate a behavior applies — a rule about the strings at a position, written as a call
     * rather than as a comparison.
     *
     * <p>The application and the whole of it, the way a comparison is. Which predicate it is and
     * what the author wrote in it are read off the call by whoever reads rules; what tells one of
     * these from another is which application of which source it is, so that a helper holding one
     * is the same rule at each of its calls.
     *
     * <p><b>Written in a body or in a clause.</b> Which of the two is not narrowed here, which is
     * where this parts from {@link Comparison}: a behavior states such a rule about one of its
     * inputs in an {@code ensures} as much as in a condition, and what the position is told apart
     * into is what the two come to between them. A predicate held to a body would be a rule of the
     * model with nowhere to be filed.
     *
     * @param behavior whose rule it is. Two behaviors calling one helper each read its predicate,
     *                 and the readings are what a coverage question is raised per
     * @param origin   which application of which module the author wrote, which is what tells one
     *                 from another wherever it is met
     */
    record Predicate(String behavior, SourceConstructOrigin origin)
            implements RuleRef {

        public Predicate {
            if (behavior == null || origin == null) {
                throw new IllegalArgumentException(
                        "a predicate of a body is one of some behavior's");
            }
            // A rule is something an author wrote. An application this compiler composed states
            // nothing about the model, so a key made from one would file a rule under a construct
            // no reader can be sent to.
            if (!origin.isWritten()) {
                throw new IllegalArgumentException(
                        "no source wrote this application, so it states no rule: " + origin);
            }
            // And written in one of the two places a behavior states such a rule. Held here rather
            // than left to the doc: an ordinal means nothing outside what it was counted in, so
            // what publishes one of these has to say which owner — and it can only be asked to say
            // that for the owners this may hold.
            if (!(origin.owner() instanceof WrittenOwner.Body)
                    && !(origin.owner() instanceof WrittenOwner.Stated)) {
                throw new IllegalArgumentException("a behavior states a rule about its strings in"
                        + " its body or in its own clauses, and this was written by "
                        + origin.owner());
            }
        }

        /**
         * What wrote the application — a definition's body, or the behavior's statement of itself.
         *
         * <p>Part of what tells this rule from every other, because {@link #origin}'s ordinal is
         * counted within it: a behavior's first clause predicate and its body's first are two
         * constructs and both are numbered zero. A reader given the number alone has an identity
         * two rules answer to.
         */
        public WrittenOwner writtenIn() {
            return origin.owner();
        }
    }

    /**
     * A clause of a behavior's {@code ensures}.
     *
     * @param rule   which rule of which clause, which is what tells one from another. Two arms of
     *               one clause may name the same case, so the author's words for it are not enough
     * @param clause what a report calls it: the name the author gave the clause, or the case the arm
     *               names where they gave none, or empty where the clause states one rule over every
     *               answer
     */
    record Ensures(BehaviorContract.RuleId rule, String clause) implements RuleRef {

        public Ensures {
            if (rule == null) {
                throw new IllegalArgumentException("an ensures rule belongs to a behavior");
            }
            // Absent is spelled as the empty string, which is what {@link #named} reads. A clause
            // stating one rule over every answer is called by the behavior's name alone, and that
            // is an answer about the clause rather than the absence of one.
            if (clause == null) {
                throw new IllegalArgumentException(
                        "a clause the author named nothing is named by nothing, not by null");
            }
        }
    }

    /**
     * What a report calls this rule.
     *
     * <p>A name and not a place. A diagnostic is built where no reader is — nothing there knows what
     * to call a source — so a place written into its text would be a line and a column with no file.
     * Where the rule is a comparison, the place is pointed at instead, by whoever holds the reading
     * it was met in.
     *
     * <p>English, like every other word this writes. What a diagnostic says instead is chosen in the
     * reader's language, from the same rule.
     */
    default String named() {
        return switch (this) {
            // What the author called it, and where they called it nothing, which of the
            // declaration's clauses it is — counted from one, as somebody reading the declaration
            // counts them. Two unnamed clauses of one declaration are two rules, and rendered by the
            // declaration alone they are one word twice.
            case Invariant i -> "invariant " + i.clause().id().declaredOn().name()
                    + i.clause().name().map(n -> " (" + n + ")")
                            .orElse(" #" + (i.clause().id().ordinal() + 1));
            // The behavior, and the words that tell one of its rules from another. A clause belongs
            // to a behavior, so there is always something to call it; only a clause stating one rule
            // over every answer has neither a name nor a case, and the behavior's own name is then
            // the whole of it.
            case Ensures e -> "ensures " + e.rule().behavior().name()
                    + (e.clause().isEmpty() ? "" : " (" + e.clause() + ")");
            // A comparison is written rather than named, so this is what it is and not what the
            // author called it. Never rendered to a reader on its own: a rule with no name gets a
            // sentence of its own, and the catalog holds those words in every language. What reaches
            // this is a caller that wanted something to call the rule anyway.
            case Comparison _ -> "the comparison";
            // A predicate is applied rather than named, so this is what it is, for the reason above.
            case Predicate _ -> "the predicate";
        };
    }
}
