package souther.compiler.semantics;

import java.util.Objects;

/**
 * A number of the arguments an operation was given, as a law counts one: an argument that is a
 * number, how many a value holds, how many elements of a container meet a statement, how many
 * different values its elements come to, or what a number of each element adds up to over them.
 *
 * @param <A> how an argument is named ({@link LawProposition})
 */
public sealed interface LawNumber<A> {

    /**
     * How many different values {@code ofTheElement} comes to over the elements of
     * {@code container}: the element itself, what a closure answers of it, or the key it is filed
     * under — two of them one value where they are equal, as a set holds one of them. Never more
     * than the container holds, and nought exactly where it holds nothing.
     */
    record HowManyDifferent<A>(A container, LawSubject<A> ofTheElement) implements LawNumber<A> {

        public HowManyDifferent {
            Objects.requireNonNull(container, "the values are of a container's elements");
            Objects.requireNonNull(ofTheElement, "and are something of each");
        }
    }

    /**
     * What {@code ofTheElement}, a number of each element of {@code container}, adds up to over
     * all of them: nought where the container holds nothing.
     */
    record SumOver<A>(A container, LawNumber<A> ofTheElement) implements LawNumber<A> {

        public SumOver {
            Objects.requireNonNull(container, "a sum is over a container's elements");
            Objects.requireNonNull(ofTheElement, "of a number of each");
        }
    }

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
     * How many of the code points of the string {@code of} are in {@code counted}. Never fewer
     * than none and never more than the string holds.
     */
    record CodePointsOf<A>(LawSubject<A> of, CodePointClass counted) implements LawNumber<A> {

        public CodePointsOf {
            Objects.requireNonNull(of, "code points are of a string");
            Objects.requireNonNull(counted, "and are counted by a class");
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
