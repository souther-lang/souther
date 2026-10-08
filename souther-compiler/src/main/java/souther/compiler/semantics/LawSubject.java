package souther.compiler.semantics;

import java.util.Objects;

/**
 * A value a law states something of: an argument, an element of one, or what a closure answers.
 *
 * @param <A> how an argument is named ({@link LawProposition})
 */
public sealed interface LawSubject<A> {

    /** The argument {@code argument} itself. */
    record Argument<A>(A argument) implements LawSubject<A> {

        public Argument {
            Objects.requireNonNull(argument, "an argument is one of the operation's");
        }
    }

    /**
     * The element of {@code container} the statement it stands in is about — named only inside a
     * statement that some element of {@code container} meets it ({@link LawProposition.SomeElement}),
     * which is what says which element that is.
     */
    record ElementOf<A>(A container) implements LawSubject<A> {

        public ElementOf {
            Objects.requireNonNull(container, "an element is of a container");
        }
    }

    /**
     * What the closure at {@code closure} answers handed the element the statement it stands in is
     * about — named only inside a statement about an element of the container the operation hands
     * that closure the elements of.
     */
    record WhatTheClosureAnswers<A>(A closure) implements LawSubject<A> {

        public WhatTheClosureAnswers {
            Objects.requireNonNull(closure, "a closure is one of the operation's arguments");
        }
    }
}
