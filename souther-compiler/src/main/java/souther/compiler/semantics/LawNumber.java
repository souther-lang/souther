package souther.compiler.semantics;

import java.util.Objects;

/**
 * A number of the arguments an operation was given, as a law counts one: an argument that is a
 * number, how many a value holds, or how many elements of a container meet a statement.
 *
 * @param <A> how an argument is named ({@link LawProposition})
 */
public sealed interface LawNumber<A> {

    /** The argument {@code argument}, which is a number. */
    record AnArgument<A>(A argument) implements LawNumber<A> {

        public AnArgument {
            Objects.requireNonNull(argument, "an argument is one of the operation's");
        }
    }

    /** How many {@code of} holds: the size of a container, the length of a string. */
    record SizeOf<A>(LawSubject<A> of) implements LawNumber<A> {

        public SizeOf {
            Objects.requireNonNull(of, "a size is of something");
        }
    }

    /**
     * How many elements of {@code container} meet {@code ofTheElement}. Never fewer than none and
     * never more than the container holds, and nought exactly where no element meets it.
     */
    record HowManyMeet<A>(A container, LawProposition<A> ofTheElement) implements LawNumber<A> {

        public HowManyMeet {
            Objects.requireNonNull(container, "the elements counted are of a container");
            Objects.requireNonNull(ofTheElement, "and meet something");
        }
    }
}
