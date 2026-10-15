package souther.compiler.semantics;

import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.List;
import java.util.Objects;

/**
 * A statement over the arguments an operation was given, as a law of it states one.
 *
 * <p>Closed, and smaller than what a condition can state: these are the words a law needs to say
 * what an observation of an operation's answer comes to, and a reader carrying one across a call
 * says each in the words the reading of a condition already has. A law that needs a word this lacks
 * is not written in a nearer one; the observation is closed instead, with the proposition the
 * domain has no words for ({@link Unsayable}).
 *
 * <p>Each side of a statement is a statement of its own. That some element meets something and
 * that none does are two answers to one question, so a denial is the other answer and not a node
 * around the first ({@link #denied}), as it is of a condition's reading.
 *
 * @param <A> how an argument is named: a word where a law is written, a declared argument once it is
 *            held to the operation's declaration
 */
public sealed interface LawProposition<A> {

    /** The other answer to the question this one answers. */
    LawProposition<A> denied();

    /** A statement that comes out the same whatever the arguments are. */
    record Always<A>(boolean holds) implements LawProposition<A> {

        @Override
        public LawProposition<A> denied() {
            return new Always<>(!holds);
        }
    }

    /** Every one of {@code parts}. */
    record All<A>(List<LawProposition<A>> parts) implements LawProposition<A> {

        public All {
            parts = List.copyOf(parts);
            if (parts.size() < 2) {
                throw new IllegalArgumentException("a conjunction is of two statements or more");
            }
        }

        @Override
        public LawProposition<A> denied() {
            return new Any<>(parts.stream().map(LawProposition::denied).toList());
        }
    }

    /** At least one of {@code parts}. */
    record Any<A>(List<LawProposition<A>> parts) implements LawProposition<A> {

        public Any {
            parts = List.copyOf(parts);
            if (parts.size() < 2) {
                throw new IllegalArgumentException("a disjunction is of two statements or more");
            }
        }

        @Override
        public LawProposition<A> denied() {
            return new All<>(parts.stream().map(LawProposition::denied).toList());
        }
    }

    /** {@code of} coming out on {@code side}: true, holding something, holding a value. */
    record Observed<A>(LawSubject<A> of, SideAnswered side) implements LawProposition<A> {

        public Observed {
            Objects.requireNonNull(of, "an observation is of something");
            Objects.requireNonNull(side, "and on some side of it");
        }

        @Override
        public LawProposition<A> denied() {
            return new Observed<>(of, new SideAnswered(side.aspect(), !side.holds()));
        }
    }

    /** {@code form states 0}, over numbers of the arguments. */
    record Compared<A>(LinearForm<LawNumber<A>> form, Rel states) implements LawProposition<A> {

        public Compared {
            Objects.requireNonNull(form, "a comparison is of a number");
            Objects.requireNonNull(states, "with nought, in some relation");
            if (form.coefs().isEmpty()) {
                throw new IllegalArgumentException(
                        "a comparison of a constant is no statement over the arguments");
            }
        }

        @Override
        public LawProposition<A> denied() {
            return new Compared<>(form, states.denied());
        }
    }

    /**
     * Some element of {@code container} meeting {@code ofTheElement} — or, where {@code holds} is
     * false, none doing so. Inside, {@link LawSubject.ElementOf} {@code container} is that element.
     */
    record SomeElement<A>(A container, LawProposition<A> ofTheElement, boolean holds)
            implements LawProposition<A> {

        public SomeElement {
            Objects.requireNonNull(container, "an element is of a container");
            Objects.requireNonNull(ofTheElement, "and meets something");
        }

        @Override
        public LawProposition<A> denied() {
            return new SomeElement<>(container, ofTheElement, !holds);
        }
    }

    /** {@code one} and {@code other} being the same value — or, where {@code holds} is false, not. */
    record Same<A>(LawSubject<A> one, LawSubject<A> other, boolean holds)
            implements LawProposition<A> {

        public Same {
            Objects.requireNonNull(one, "a sameness is of two values");
            Objects.requireNonNull(other, "a sameness is of two values");
        }

        @Override
        public LawProposition<A> denied() {
            return new Same<>(one, other, !holds);
        }
    }
}
