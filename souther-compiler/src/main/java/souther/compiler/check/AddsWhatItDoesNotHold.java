package souther.compiler.check;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.proof.Slot;
import souther.compiler.semantics.AnswerAspect;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.semantics.SideAnswered;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Set;
import java.util.function.BiFunction;

/**
 * What an operation adds to one of its arguments: its answer holds exactly what that argument
 * holds and the values it was handed, so it holds as many as the argument and one for each value
 * handed that the argument did not hold yet.
 *
 * <p>Read off the operation's laws and not off which operation it is, so every operation whose
 * laws say so is read alike. Two laws, each saying half: the law of how many its answer holds —
 * a set given a value and a map given a value under a key say it in two cases, holding the value
 * already and not; a union says it as a count of the elements of the other argument no element
 * of the first is — and a law of which values its answer holds, a value being in it exactly where
 * it is one handed or one the argument held. Both are what lets a walk whose step is the
 * operation over what it carried be counted by induction: what it ends with holds every value it
 * was handed, once each.
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

    /**
     * How whether a container holds a value is asked: {@code operation}, handed the value at
     * {@code value} and the container at {@code container} — an operation whose law of truth says
     * some element of the container, or some key of it, is the value.
     */
    record Asked(ValueName.Stdlib.Operation operation, DeclaredArgument value,
                 DeclaredArgument container) {

        public Asked {
            Objects.requireNonNull(operation, "some operation asks it");
            Objects.requireNonNull(value, "it is handed the value");
            Objects.requireNonNull(container, "it is handed the container");
            if (value.position() == container.position()
                    || value.of().arity() != 2 || container.of().arity() != 2) {
                throw new IllegalArgumentException(operation + " is handed the value and the"
                        + " container and nothing else");
            }
        }
    }

    /**
     * What {@code operation} adds beside what the holder holds — or null where its law of how many
     * it answers, {@code law}, says something else, or nothing stated of its answer beside
     * others, {@code statedBeside}, says the answer holds exactly what was added and what the
     * holder held.
     *
     * <p>Both, and neither alone. How many the answer holds is not which values it holds: an
     * answer one larger for each value not held yet could hold other values than the holder's,
     * and a walk counted by it would count values it was never handed. What the answer holds is
     * said by the law of membership in it — a value is in it exactly where it is one added or one
     * the holder held — and the count is then the count of those, which the law of how many says
     * in the same words.
     *
     * <p>Which operation the law of membership asks is the law's to say, and nothing here names
     * one: it is read as asking whether a container holds a value only where that operation's own
     * law of truth says so ({@code asking}). The law was held to the operations' declarations when
     * it was bound, so the operation it names takes the containers it is handed.
     *
     * @param asking how {@code in} asks whether a container holds a value as {@code of} says, or
     *               null where its law of truth says no such thing
     */
    static AddsWhatItDoesNotHold of(ValueName operation, OperationLaw<DeclaredArgument> law,
                                    List<LawProposition<Slot>> statedBeside,
                                    BiFunction<ValueName.Stdlib.Operation, Of, Asked> asking) {
        AddsWhatItDoesNotHold counted = countedBy(law);
        if (counted == null) {
            return null;
        }
        for (LawProposition<Slot> each : statedBeside) {
            if (holdsExactly(counted, operation, each, asking)) {
                return counted;
            }
        }
        return null;
    }

    /** What {@code law} counts the operation as adding, or null where it counts something
     *  else: the half of {@link #of} said by how many the answer holds. */
    static AddsWhatItDoesNotHold countedBy(OperationLaw<DeclaredArgument> law) {
        if (!(law instanceof OperationLaw.Size<DeclaredArgument> size)) {
            return null;
        }
        LinearForm<LawNumber<DeclaredArgument>> always = size.unconditional();
        return always != null ? theElementsOf(always) : oneValue(size.cases());
    }

    /**
     * Whether {@code stated} says a value is in {@code operation}'s answer exactly where it is one
     * {@code adds} adds or one its holder holds: {@code in(y, answer) ⇔ in(y, added) ∨ in(y,
     * holder)}, as an equivalence is written ({@code any(all(a, b), all(¬a, ¬b))}, the parts of
     * each in either order).
     */
    private static boolean holdsExactly(AddsWhatItDoesNotHold adds, ValueName operation,
                                        LawProposition<Slot> stated,
                                        BiFunction<ValueName.Stdlib.Operation, Of, Asked> asking) {
        if (!(stated instanceof LawProposition.Any<Slot>(List<LawProposition<Slot>> either))
                || either.size() != 2) {
            return false;
        }
        for (List<LawProposition<Slot>> halves : List.of(either, either.reversed())) {
            if (halves.getFirst() instanceof LawProposition.All<Slot>(
                    List<LawProposition<Slot>> both) && both.size() == 2
                    && halves.getLast() instanceof LawProposition.All<Slot>(
                            List<LawProposition<Slot>> neither)
                    && Set.copyOf(neither).equals(Set.of(both.getFirst().denied(),
                            both.getLast().denied()))) {
                for (List<LawProposition<Slot>> sides : List.of(both, both.reversed())) {
                    if (saysTheAnswerHolds(adds, operation, sides.getFirst(), sides.getLast(),
                            asking)) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    /** Whether {@code inTheAnswer} says any value is in {@code operation}'s answer, handed its own
     *  arguments, and {@code where} says exactly where the value is one added or one held. */
    private static boolean saysTheAnswerHolds(AddsWhatItDoesNotHold adds, ValueName operation,
                                              LawProposition<Slot> inTheAnswer,
                                              LawProposition<Slot> where,
                                              BiFunction<ValueName.Stdlib.Operation, Of, Asked>
                                                      asking) {
        Asked inTheHolder = askedBy(inTheAnswer, switch (adds) {
            case OneValue one -> one.of();
            case TheElementsOf _ -> Of.ELEMENTS;
        }, asking);
        List<LawSubject<Slot>> asked = inTheHolder == null ? null
                : membershipIn(inTheHolder, inTheAnswer);
        if (asked == null
                || !(asked.getLast() instanceof LawSubject.AnswerOf<Slot>(
                        ValueName.Stdlib.Operation answered, List<LawSubject<Slot>> args))
                || !answered.equals(operation) || !handedItsOwn(args)
                || !(where instanceof LawProposition.Any<Slot>(
                        List<LawProposition<Slot>> parts)) || parts.size() != 2) {
            return false;
        }
        LawSubject<Slot> any = asked.getFirst();
        LawProposition<Slot> held = membership(inTheHolder, any,
                new LawSubject.Argument<>(new Slot.Place(adds.holder().position())));
        if (!parts.contains(held)) {
            return false;
        }
        LawProposition<Slot> other = parts.getFirst().equals(held) ? parts.getLast()
                : parts.getFirst();
        LawProposition<Slot> added = switch (adds) {
            case OneValue one -> new LawProposition.Same<>(any,
                    new LawSubject.Argument<>(new Slot.Place(one.value().position())), true);
            case TheElementsOf elements -> {
                Asked inWhatIsAdded = askedBy(other, Of.ELEMENTS, asking);
                yield inWhatIsAdded == null ? null : membership(inWhatIsAdded, any,
                        new LawSubject.Argument<>(new Slot.Place(elements.from().position())));
            }
        };
        return other.equals(added);
    }

    /** How the operation whose answer {@code stated} observes asks whether a container holds a
     *  value as {@code of} says — or null where it observes none, or that operation's law of
     *  truth says no such thing. */
    private static Asked askedBy(LawProposition<Slot> stated, Of of,
                                 BiFunction<ValueName.Stdlib.Operation, Of, Asked> asking) {
        return stated instanceof LawProposition.Observed<Slot>(
                LawSubject.AnswerOf<Slot>(ValueName.Stdlib.Operation in, var _), var _)
                ? asking.apply(in, of) : null;
    }

    /** That {@code value} is in {@code container}, as a law says it: {@code in}'s answer, handed
     *  each where it takes it, holding. */
    private static LawProposition<Slot> membership(Asked in, LawSubject<Slot> value,
                                                   LawSubject<Slot> container) {
        List<LawSubject<Slot>> handed = new ArrayList<>(List.of(value, value));
        handed.set(in.container().position(), container);
        return new LawProposition.Observed<>(new LawSubject.AnswerOf<>(in.operation(), handed),
                new SideAnswered(AnswerAspect.TRUTH, true));
    }

    /** The value and the container {@code stated} says the one is in, in that order, by
     *  {@code in}'s answer holding, the value being any value at all — or null where it says
     *  something else. */
    private static List<LawSubject<Slot>> membershipIn(Asked in, LawProposition<Slot> stated) {
        return stated instanceof LawProposition.Observed<Slot>(
                LawSubject.AnswerOf<Slot>(ValueName.Stdlib.Operation asked,
                        List<LawSubject<Slot>> args), SideAnswered side)
                && asked.equals(in.operation())
                && side.equals(new SideAnswered(AnswerAspect.TRUTH, true))
                && args.size() == 2
                && args.get(in.value().position()) instanceof LawSubject.Argument<Slot>(
                        Slot.Every _)
                ? List.of(args.get(in.value().position()), args.get(in.container().position()))
                : null;
    }

    /** Whether {@code args} are an operation's own arguments, each where it was handed. */
    private static boolean handedItsOwn(List<LawSubject<Slot>> args) {
        for (int at = 0; at < args.size(); at++) {
            if (!args.get(at).equals(new LawSubject.Argument<>(new Slot.Place(at)))) {
                return false;
            }
        }
        return true;
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
