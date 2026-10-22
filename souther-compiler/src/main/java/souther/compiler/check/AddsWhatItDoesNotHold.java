package souther.compiler.check;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.OperationLaw;

import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * What an operation's law of how many it answers says it adds to one of its arguments: as many as
 * that argument holds, and one for each value it is handed that the argument does not hold yet.
 *
 * <p>Read off the law and not off which operation it is, so every operation whose law says so is
 * read alike. A set given a value ({@code Set.insert}) and a map given a value under a key
 * ({@code Map.insert}, {@code Map.updateOrInsert}) say it in two cases, holding the value already
 * and not; a union ({@code Set.union}) says it as a count of the elements of the other argument
 * that no element of the first is. Either is what lets a walk whose step is the operation over
 * what it carried be counted by induction: what it ends with holds every value it was handed once.
 */
public sealed interface AddsWhatItDoesNotHold {

    /** The argument the answer holds all of, beside what it adds. */
    DeclaredArgument holder();

    /**
     * One value, handed at {@code value}: the holder holding it already as {@code of} says —
     * among its elements, or among its keys — and one more where it does not.
     */
    record OneValue(DeclaredArgument holder, DeclaredArgument value, Of of)
            implements AddsWhatItDoesNotHold {

        public OneValue {
            Objects.requireNonNull(holder, "a value is added to something");
            Objects.requireNonNull(value, "some value is added");
            Objects.requireNonNull(of, "it is held as an element or as a key");
        }
    }

    /** The elements of the container at {@code from}, each the holder does not hold. */
    record TheElementsOf(DeclaredArgument holder, DeclaredArgument from)
            implements AddsWhatItDoesNotHold {

        public TheElementsOf {
            Objects.requireNonNull(holder, "elements are added to something");
            Objects.requireNonNull(from, "they are some container's");
        }
    }

    /** Where in the holder a value added is looked for. */
    enum Of { ELEMENTS, KEYS }

    /** What {@code law} says the operation adds, or null where it says something else. */
    static AddsWhatItDoesNotHold of(OperationLaw<DeclaredArgument> law) {
        if (!(law instanceof OperationLaw.Size<DeclaredArgument> size)) {
            return null;
        }
        LinearForm<LawNumber<DeclaredArgument>> always = size.unconditional();
        return always != null ? theElementsOf(always) : oneValue(size.cases());
    }

    /** {@code size(h) + howManyMeet(f, no element of h is the element of f)}. */
    private static AddsWhatItDoesNotHold theElementsOf(
            LinearForm<LawNumber<DeclaredArgument>> form) {
        if (form.constant().signum() != 0 || form.coefs().size() != 2
                || !form.coefs().values().stream().allMatch(ExactRatio.ONE::equals)) {
            return null;
        }
        DeclaredArgument holder = null;
        LawNumber.HowManyMeet<DeclaredArgument> added = null;
        for (LawNumber<DeclaredArgument> each : form.coefs().keySet()) {
            if (each instanceof LawNumber.SizeOf<DeclaredArgument>(
                    LawSubject.Argument<DeclaredArgument>(DeclaredArgument held))) {
                holder = held;
            } else if (each instanceof LawNumber.HowManyMeet<DeclaredArgument> meet) {
                added = meet;
            }
        }
        if (holder == null || added == null || holder.equals(added.container())
                || !(added.ofTheElement() instanceof LawProposition.SomeElement<DeclaredArgument>(
                        DeclaredArgument in, LawProposition<DeclaredArgument> ofIt, boolean holds))
                || holds || !in.equals(holder)
                || !sameValue(ofIt, new LawSubject.ElementOf<>(holder),
                        new LawSubject.ElementOf<>(added.container()))) {
            return null;
        }
        return new TheElementsOf(holder, added.container());
    }

    /** Two cases: {@code size(h)} where h holds the value, {@code size(h) + 1} where not. */
    private static AddsWhatItDoesNotHold oneValue(
            List<OperationLaw.Size.Case<DeclaredArgument>> cases) {
        if (cases.size() != 2) {
            return null;
        }
        OneValue held = null;
        OneValue notHeld = null;
        for (OperationLaw.Size.Case<DeclaredArgument> each : cases) {
            if (!(each.where() instanceof LawProposition.SomeElement<DeclaredArgument>(
                    DeclaredArgument holder, LawProposition<DeclaredArgument> ofIt,
                    boolean holds))) {
                return null;
            }
            OneValue added = valueHeldBy(holder, ofIt);
            if (added == null || !each.equalTo().equals(new LinearForm<>(
                    ExactRatio.of(holds ? 0 : 1), Map.of(new LawNumber.SizeOf<>(
                            new LawSubject.Argument<>(holder)), ExactRatio.ONE)))) {
                return null;
            }
            if (holds) {
                held = added;
            } else {
                notHeld = added;
            }
        }
        return held != null && held.equals(notHeld) ? held : null;
    }

    /** The value {@code ofIt}, said of an element of {@code holder}, says the element is. */
    private static OneValue valueHeldBy(DeclaredArgument holder,
                                        LawProposition<DeclaredArgument> ofIt) {
        if (!(ofIt instanceof LawProposition.Same<DeclaredArgument>(
                LawSubject<DeclaredArgument> one, LawSubject<DeclaredArgument> other,
                boolean holds)) || !holds) {
            return null;
        }
        for (List<LawSubject<DeclaredArgument>> pair : List.of(List.of(one, other),
                List.of(other, one))) {
            if (pair.get(1) instanceof LawSubject.Argument<DeclaredArgument>(
                    DeclaredArgument value) && !value.equals(holder)) {
                if (pair.get(0) instanceof LawSubject.ElementOf<DeclaredArgument>(
                        DeclaredArgument in) && in.equals(holder)) {
                    return new OneValue(holder, value, Of.ELEMENTS);
                }
                if (pair.get(0) instanceof LawSubject.KeyOf<DeclaredArgument>(
                        DeclaredArgument in) && in.equals(holder)) {
                    return new OneValue(holder, value, Of.KEYS);
                }
            }
        }
        return null;
    }

    /** Whether {@code stated} says {@code one} and {@code other} are the same value. */
    private static boolean sameValue(LawProposition<DeclaredArgument> stated,
                                     LawSubject<DeclaredArgument> one,
                                     LawSubject<DeclaredArgument> other) {
        return stated instanceof LawProposition.Same<DeclaredArgument>(
                LawSubject<DeclaredArgument> a, LawSubject<DeclaredArgument> b, boolean holds)
                && holds
                && ((a.equals(one) && b.equals(other)) || (a.equals(other) && b.equals(one)));
    }
}
