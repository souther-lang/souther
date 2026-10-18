package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;
import souther.compiler.semantics.SideAnswered;
import souther.compiler.types.TypeSymbol;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.OptionalLong;
import java.util.function.Function;

/**
 * What a law of the library says at one call of its operation, read in whatever environment the
 * call's names are read in.
 *
 * <p>One reading of a law for every reader of one. The reading of an input and the discharge of a
 * rule both take what an operation's law says ({@link BoundOperationFacts#settled}) at a call, and
 * each reads the arguments in an environment of its own. Two readings of the law would be a program
 * measured one way and checked another the first time one of them learned a part of a law the
 * other did not — an element of a filter written out that one of them found and the other never
 * looked for. So how a law is taken apart is decided here: its parts joined as they are joined, and
 * every number of it asked as the number it is.
 *
 * <p>Decided here as well is what a law says of the elements of a container written out, where that
 * comes out the same on every run ({@link ElementsWrittenOut}). Some element of {@code [c, 3]} is
 * above two whatever {@code c} is, and how many of them are is not; the first is this reading's
 * answer, and the second is each reader's own. A reader is asked for a part only where this did not
 * settle it: what an argument comes out as, how numbers of the arguments stand, some element of a
 * container no walk writes out, two values being one — each of which is what that reader's
 * vocabulary says, or that it says nothing.
 */
public final class LawAtACall {

    private LawAtACall() {
    }

    /**
     * What a law's reading asks of a reader: where the call's arguments stand in its environment
     * {@code E}, its own answer {@code P} to each part of a law this does not settle, and its own
     * answer {@code N} to each number of one.
     *
     * @param <E> the environment
     * @param <P> the reader's answer to a part of a law
     * @param <N> the reader's answer to a number of one
     */
    public interface Reading<E, P, N> extends ElementsWrittenOut.Reading<E> {

        /** The value the call was handed as {@code argument}, where it was written — or null where
         *  the call was handed none there. */
        ElementsWrittenOut.Stood<E> argument(DeclaredArgument argument);

        /** A part saying the same whatever the arguments are. */
        P settles(LawProposition.Always<DeclaredArgument> always);

        /** Every one of {@code parts}, each read as {@code each}. */
        P joins(LawProposition.All<DeclaredArgument> all, List<P> each);

        /** Some one of {@code any}'s parts, each read where the reader asks for it by
         *  {@code part}. */
        P eitherOf(LawProposition.Any<DeclaredArgument> any,
                   Function<LawProposition<DeclaredArgument>, P> part);

        /** A subject coming out on a side. */
        P observed(LawProposition.Observed<DeclaredArgument> observed);

        /** A form over numbers of the arguments standing against nought. */
        P compared(LawProposition.Compared<DeclaredArgument> compared);

        /** Some element of a container meeting a statement, where this did not settle it. */
        P someElement(LawProposition.SomeElement<DeclaredArgument> some);

        /** Some element of a container written out meeting a statement, settled the same on every
         *  run: {@code someMeets} whether one does, before {@code some} says which it states. */
        P writtenOut(LawProposition.SomeElement<DeclaredArgument> some, boolean someMeets);

        /** Two subjects being one value, or not. */
        P same(LawProposition.Same<DeclaredArgument> same);

        /** A number of the arguments, where this did not settle it. */
        N counted(LawNumber<DeclaredArgument> number);

        /** How many elements of a container written out meet a statement, the same on every
         *  run. */
        N writtenOut(LawNumber.HowManyMeet<DeclaredArgument> number, long many);
    }

    /**
     * Whether {@code arm} is taken where the optional it matches holds a value, or where it holds
     * none — or null where it is taken on both, or on neither. The side of the answer a law of
     * presence is about, where an arm is what asks it.
     */
    public static Boolean presentWhereTaken(Core.Case arm) {
        if (arm.pattern() == null) {
            return null;
        }
        boolean some = arm.pattern().takes(TypeSymbol.SOME);
        boolean none = arm.pattern().takes(TypeSymbol.NONE);
        return some == none ? null : some;
    }

    /** {@code law}, a statement over the call's arguments, as {@code reading} answers it. */
    public static <E, P, N> P of(LawProposition<DeclaredArgument> law, Reading<E, P, N> reading) {
        return switch (law) {
            case LawProposition.Always<DeclaredArgument> always -> reading.settles(always);
            case LawProposition.All<DeclaredArgument> all -> {
                List<P> each = new ArrayList<>(all.parts().size());
                for (LawProposition<DeclaredArgument> part : all.parts()) {
                    each.add(of(part, reading));
                }
                yield reading.joins(all, each);
            }
            case LawProposition.Any<DeclaredArgument> any ->
                    reading.eitherOf(any, part -> of(part, reading));
            case LawProposition.Observed<DeclaredArgument> observed -> reading.observed(observed);
            case LawProposition.Compared<DeclaredArgument> compared -> reading.compared(compared);
            case LawProposition.SomeElement<DeclaredArgument> some -> {
                Boolean meets = someWrittenOutMeets(some, reading);
                yield meets != null ? reading.writtenOut(some, meets) : reading.someElement(some);
            }
            case LawProposition.Same<DeclaredArgument> same -> reading.same(same);
        };
    }

    /** {@code number}, a number of the call's arguments, as {@code reading} answers it. */
    public static <E, P, N> N number(LawNumber<DeclaredArgument> number,
                                     Reading<E, P, N> reading) {
        if (number instanceof LawNumber.HowManyMeet<DeclaredArgument> counted) {
            OptionalLong many = howManyWrittenOutMeet(counted, reading);
            if (many.isPresent()) {
                return reading.writtenOut(counted, many.getAsLong());
            }
        }
        return reading.counted(number);
    }

    /**
     * Whether some element of the container {@code some} names, written out, meets what it states
     * on every run — true where one there on every run meets it on every run, false where each is
     * there on no run or meets it on none — or null where that turns on the run, or the container
     * is not written out.
     */
    private static <E> Boolean someWrittenOutMeets(LawProposition.SomeElement<DeclaredArgument> some,
                                                   Reading<E, ?, ?> reading) {
        List<ElementsWrittenOut.Occurrence<E>> each = writtenOut(some.container(), reading);
        if (each == null) {
            return null;
        }
        boolean turns = false;
        for (ElementsWrittenOut.Occurrence<E> one : each) {
            Boolean there = ElementsWrittenOut.onEveryRun(one, reading);
            Boolean meets = Boolean.FALSE.equals(there) ? Boolean.FALSE
                    : meets(some.ofTheElement(), some.container(), one.value(), reading);
            if (Boolean.TRUE.equals(there) && Boolean.TRUE.equals(meets)) {
                return true;
            }
            turns |= !Boolean.FALSE.equals(meets);
        }
        return turns ? null : false;
    }

    /** How many elements of the container {@code counted} names, written out, meet what it states
     *  on every run, or empty where that turns on the run or the container is not written out. */
    private static <E> OptionalLong howManyWrittenOutMeet(
            LawNumber.HowManyMeet<DeclaredArgument> counted, Reading<E, ?, ?> reading) {
        List<ElementsWrittenOut.Occurrence<E>> each = writtenOut(counted.container(), reading);
        if (each == null) {
            return OptionalLong.empty();
        }
        long many = 0;
        for (ElementsWrittenOut.Occurrence<E> one : each) {
            Boolean there = ElementsWrittenOut.onEveryRun(one, reading);
            Boolean meets = Boolean.FALSE.equals(there) ? Boolean.FALSE
                    : meets(counted.ofTheElement(), counted.container(), one.value(), reading);
            if (there == null || meets == null) {
                return OptionalLong.empty();
            }
            many += meets ? 1 : 0;
        }
        return OptionalLong.of(many);
    }

    /** Every element of the container the call was handed as {@code container}, or null where it
     *  is no container a walk writes out. */
    private static <E> List<ElementsWrittenOut.Occurrence<E>> writtenOut(
            DeclaredArgument container, Reading<E, ?, ?> reading) {
        ElementsWrittenOut.Stood<E> given = reading.argument(container);
        return given != null && ElementsWrittenOut.of(given, reading)
                instanceof ElementsWrittenOut.Walked.Each<E>(var each) ? each : null;
    }

    /**
     * Whether {@code element}, an element of {@code container}, meets {@code law} on every run, or
     * null where that turns on the run or this cannot say.
     *
     * <p>Only what folds to a constant: the element itself, the closure's answer on the
     * application handing it the element, and numbers of either, each read as the reader folds a
     * value ({@link ElementsWrittenOut.Reading#folded}). Anything else is the reader's to read over
     * the element, which it does where this says null.
     */
    private static <E> Boolean meets(LawProposition<DeclaredArgument> law,
                                     DeclaredArgument container,
                                     ElementsWrittenOut.Stood<E> element,
                                     Reading<E, ?, ?> reading) {
        return switch (law) {
            case LawProposition.Always<DeclaredArgument>(boolean holds) -> holds;
            case LawProposition.All<DeclaredArgument>(var parts) -> {
                boolean turns = false;
                for (LawProposition<DeclaredArgument> part : parts) {
                    Boolean one = meets(part, container, element, reading);
                    if (Boolean.FALSE.equals(one)) {
                        yield false;
                    }
                    turns |= one == null;
                }
                yield turns ? null : true;
            }
            case LawProposition.Any<DeclaredArgument>(var parts) -> {
                boolean turns = false;
                for (LawProposition<DeclaredArgument> part : parts) {
                    Boolean one = meets(part, container, element, reading);
                    if (Boolean.TRUE.equals(one)) {
                        yield true;
                    }
                    turns |= one == null;
                }
                yield turns ? null : false;
            }
            case LawProposition.Observed<DeclaredArgument>(var of, SideAnswered side) -> {
                ElementsWrittenOut.Stood<E> value = valueOf(of, container, element, reading);
                if (value == null) {
                    yield null;
                }
                Boolean holds = switch (side.aspect()) {
                    case TRUTH -> reading.folded(value).orElse(null) instanceof Boolean truth
                            ? truth : null;
                    case EMPTINESS -> {
                        OptionalLong size = ElementsWrittenOut.sizeOf(value, reading);
                        yield size.isPresent() ? size.getAsLong() > 0 : null;
                    }
                    case PRESENCE -> null;
                };
                yield holds == null ? null : holds == side.holds();
            }
            case LawProposition.Compared<DeclaredArgument>(var form, var states) -> {
                ExactRatio total = form.constant();
                for (Map.Entry<LawNumber<DeclaredArgument>, ExactRatio> each
                        : form.coefs().entrySet()) {
                    ExactRatio value = numberOf(each.getKey(), container, element, reading);
                    ExactRatio before = total;
                    total = value == null ? null
                            : value.times(each.getValue()).flatMap(before::plus).orNull();
                    if (total == null) {
                        yield null;
                    }
                }
                yield states.holds(total.signum());
            }
            case LawProposition.SomeElement<DeclaredArgument> _,
                 LawProposition.Same<DeclaredArgument> _ -> null;
        };
    }

    /** The number {@code number} is of {@code element} and the call's arguments, folded, or null
     *  where it folds to none. */
    private static <E> ExactRatio numberOf(LawNumber<DeclaredArgument> number,
                                           DeclaredArgument container,
                                           ElementsWrittenOut.Stood<E> element,
                                           Reading<E, ?, ?> reading) {
        return switch (number) {
            case LawNumber.AnArgument<DeclaredArgument>(DeclaredArgument at) -> {
                ElementsWrittenOut.Stood<E> value =
                        valueOf(new LawSubject.Argument<>(at), container, element, reading);
                BigDecimal folded = value == null ? null
                        : FoldedValue.number(reading.folded(value));
                yield folded == null ? null : ExactRatio.of(folded);
            }
            case LawNumber.SizeOf<DeclaredArgument>(var of) -> {
                ElementsWrittenOut.Stood<E> value = valueOf(of, container, element, reading);
                OptionalLong size = value == null ? OptionalLong.empty()
                        : ElementsWrittenOut.sizeOf(value, reading);
                yield size.isPresent() ? ExactRatio.of(size.getAsLong()) : null;
            }
            case LawNumber.HowManyMeet<DeclaredArgument> _,
                 LawNumber.HowManyDifferent<DeclaredArgument> _,
                 LawNumber.SumOver<DeclaredArgument> _,
                 LawNumber.CodePointsOf<DeclaredArgument> _ -> null;
        };
    }

    /**
     * The value {@code of} names where {@code element} is the element of {@code container}: the
     * element itself, the body of the closure handed as an argument on the application handing it
     * the element, or an argument — or null where it names anything else, or the closure is no
     * block of one parameter.
     */
    private static <E> ElementsWrittenOut.Stood<E> valueOf(LawSubject<DeclaredArgument> of,
                                                           DeclaredArgument container,
                                                           ElementsWrittenOut.Stood<E> element,
                                                           Reading<E, ?, ?> reading) {
        return switch (of) {
            case LawSubject.ElementOf<DeclaredArgument>(DeclaredArgument at) ->
                    at.equals(container) ? element : null;
            case LawSubject.WhatTheClosureAnswers<DeclaredArgument>(DeclaredArgument at) -> {
                ElementsWrittenOut.Stood<E> handed = reading.argument(at);
                ElementsWrittenOut.Stood<E> closure = handed == null ? null
                        : reading.standing(handed.value(), handed.at());
                if (closure == null
                        || !(Core.withoutStanding(closure.value()) instanceof Core.Block block)
                        || block.params().size() != 1 || block.params().getFirst() == null
                        || block.params().getFirst().binding() == null) {
                    yield null;
                }
                yield new ElementsWrittenOut.Stood<>(block.body(), reading.handing(closure.at(),
                        block.params().getFirst().binding(), element));
            }
            case LawSubject.Argument<DeclaredArgument>(DeclaredArgument at) ->
                    reading.argument(at);
            case LawSubject.KeyOf<DeclaredArgument> _,
                 LawSubject.AnswerOf<DeclaredArgument> _ -> null;
        };
    }
}
