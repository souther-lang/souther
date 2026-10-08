package souther.compiler.semantics;

import souther.compiler.numeric.LinearForm;

import java.util.Objects;

/**
 * What an observation of an operation's answer comes to, over the arguments it was given.
 *
 * <p>One account of what is known of an answer, in two kinds, because they are two relations. That
 * a filter's answer holds something is a truth, and it is equivalent to a truth over the arguments;
 * how many it holds is a number, and it is equal to a number of them. Read as one, carrying a number
 * across a call would turn it into a statement on the way, and which statement would be the reader's
 * choice and not the law's.
 *
 * <p>Exact, and about an answer that was given: what holds of a call that stops on its arguments is
 * not what these say, so a law is the equivalence where the operation answers and is silent on
 * where it does not.
 *
 * @param <A> how an argument is named ({@link LawProposition})
 */
public sealed interface OperationLaw<A> {

    /** Which observation of the answer this law is about. */
    Observed observed();

    /**
     * The answer comes out on {@code aspect}'s holding side — true, holding something, holding a
     * value — exactly where {@code equivalentTo} holds of the arguments.
     */
    record Observation<A>(AnswerAspect aspect, LawProposition<A> equivalentTo)
            implements OperationLaw<A> {

        public Observation {
            Objects.requireNonNull(aspect, "an observation is on some side of the answer");
            Objects.requireNonNull(equivalentTo, "and comes to something");
        }

        @Override
        public Observed observed() {
            return Observed.of(aspect);
        }
    }

    /** How many the answer holds is {@code equalTo}, a number of the arguments. */
    record Size<A>(LinearForm<LawNumber<A>> equalTo) implements OperationLaw<A> {

        public Size {
            Objects.requireNonNull(equalTo, "a size is some number");
        }

        @Override
        public Observed observed() {
            return Observed.SIZE;
        }
    }

    /**
     * The observations of an answer a law can be about: its sides, and how many it holds.
     *
     * <p>Each is a question asked of every operation whose answer has it, and settled once, by a
     * law or by a closing ({@link Unsayable}).
     */
    enum Observed {
        TRUTH,
        EMPTINESS,
        PRESENCE,
        SIZE;

        /** The observation of a side of the answer. */
        public static Observed of(AnswerAspect aspect) {
            return switch (aspect) {
                case TRUTH -> TRUTH;
                case EMPTINESS -> EMPTINESS;
                case PRESENCE -> PRESENCE;
            };
        }
    }
}
