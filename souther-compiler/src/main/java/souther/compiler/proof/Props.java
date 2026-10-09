package souther.compiler.proof;

import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;

import java.util.ArrayList;
import java.util.List;

/**
 * Statements over values put together the way the proofs here need them: a conjunction or a
 * disjunction of any number of parts, which says nothing more than its parts, and a comparison of a
 * form that may have come to a constant.
 *
 * <p>Folded as they are made, so that a part settled either way is not carried as a part: a
 * conjunction holding a statement that never holds never holds, and one holding only statements that
 * always hold always does. Nothing else is decided here.
 */
final class Props {

    private Props() {}

    static <A> LawProposition<A> always(boolean holds) {
        return new LawProposition.Always<>(holds);
    }

    /** Every one of {@code parts}. */
    static <A> LawProposition<A> all(List<LawProposition<A>> parts) {
        List<LawProposition<A>> kept = new ArrayList<>();
        for (LawProposition<A> part : parts) {
            switch (part) {
                case LawProposition.Always<A>(boolean holds) when holds -> { }
                case LawProposition.Always<A> never -> {
                    return never;
                }
                case LawProposition.All<A>(List<LawProposition<A>> inner) -> kept.addAll(inner);
                default -> kept.add(part);
            }
        }
        return kept.isEmpty() ? always(true)
                : kept.size() == 1 ? kept.get(0) : new LawProposition.All<>(kept);
    }

    /** At least one of {@code parts}. */
    static <A> LawProposition<A> any(List<LawProposition<A>> parts) {
        List<LawProposition<A>> kept = new ArrayList<>();
        for (LawProposition<A> part : parts) {
            switch (part) {
                case LawProposition.Always<A>(boolean holds) when !holds -> { }
                case LawProposition.Always<A> ever -> {
                    return ever;
                }
                case LawProposition.Any<A>(List<LawProposition<A>> inner) -> kept.addAll(inner);
                default -> kept.add(part);
            }
        }
        return kept.isEmpty() ? always(false)
                : kept.size() == 1 ? kept.get(0) : new LawProposition.Any<>(kept);
    }

    static <A> LawProposition<A> both(LawProposition<A> one, LawProposition<A> other) {
        return all(List.of(one, other));
    }

    static <A> LawProposition<A> either(LawProposition<A> one, LawProposition<A> other) {
        return any(List.of(one, other));
    }

    /** {@code one} exactly where {@code other}. */
    static <A> LawProposition<A> same(LawProposition<A> one, LawProposition<A> other) {
        return either(both(one, other), both(one.denied(), other.denied()));
    }

    /** {@code form states 0}, settled where the form is a constant. */
    static <A> LawProposition<A> compared(LinearForm<LawNumber<A>> form, Rel states) {
        if (form.coefs().isEmpty()) {
            return always(states.holds(form.constant().signum()));
        }
        return new LawProposition.Compared<>(form, states);
    }

    /** {@code one states other}. */
    static <A> LawProposition<A> compared(LinearForm<LawNumber<A>> one, Rel states,
                                          LinearForm<LawNumber<A>> other) {
        return compared(minus(one, other), states);
    }

    static <A> LinearForm<A> plus(LinearForm<A> one, LinearForm<A> other) {
        return held(one.plus(other));
    }

    static <A> LinearForm<A> minus(LinearForm<A> one, LinearForm<A> other) {
        return held(one.minus(other));
    }

    static <A> LinearForm<A> constant(long value) {
        return LinearForm.constant(ExactRatio.of(value));
    }

    /** {@code form}, which the arithmetic holds exactly; a sum it cannot hold stops the proof. */
    static <A> LinearForm<A> held(ExactAnswer<LinearForm<A>> form) {
        if (form instanceof ExactAnswer.Held<LinearForm<A>>(LinearForm<A> value)) {
            return value;
        }
        throw new Reading.Stopped(new Library.Settled.Open(
                new Unproved.DoesNotFollow(Unproved.Obligation.THE_STATEMENT)));
    }
}
