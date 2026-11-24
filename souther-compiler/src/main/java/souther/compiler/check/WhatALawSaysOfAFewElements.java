package souther.compiler.check;

import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.semantics.LawNumber;
import souther.compiler.semantics.LawProposition;
import souther.compiler.semantics.LawSubject;

import java.util.Map;

/**
 * What a law of an operation says of every call whose container holds no element or one.
 *
 * <p>A container that small fixes some numbers a law names whatever the elements are: how many it
 * holds is its size, and how many different values its elements come to is its size too, since one
 * element comes to one value and none come to none. So a law stated over those numbers alone is
 * true or false of every such call, and that is a fact about the operation the law states and not a
 * reading of any rule: {@code List.allDistinctBy}'s law, that the elements come to as many
 * different keys as there are elements, holds of a list of one whatever the key.
 *
 * <p>Anything else a law names — an element itself, what the closure answers of one, another
 * argument — is not settled by the size, and a law that turns on it says nothing here.
 */
final class WhatALawSaysOfAFewElements {

    private WhatALawSaysOfAFewElements() {
    }

    /**
     * Whether {@code law} holds of every call whose argument at {@code container} holds
     * {@code size} elements, or null where the size does not settle it.
     *
     * @param size nought or one
     */
    static Boolean holds(LawProposition<DeclaredArgument> law, int container, int size) {
        if (size < 0 || size > 1) {
            throw new IllegalArgumentException("a few elements are none or one: " + size);
        }
        return switch (law) {
            case LawProposition.Always<DeclaredArgument> always -> always.holds();
            case LawProposition.All<DeclaredArgument> all -> {
                boolean unsettled = false;
                for (LawProposition<DeclaredArgument> part : all.parts()) {
                    Boolean each = holds(part, container, size);
                    if (Boolean.FALSE.equals(each)) {
                        yield false;
                    }
                    unsettled |= each == null;
                }
                yield unsettled ? null : true;
            }
            case LawProposition.Any<DeclaredArgument> any -> {
                boolean unsettled = false;
                for (LawProposition<DeclaredArgument> part : any.parts()) {
                    Boolean each = holds(part, container, size);
                    if (Boolean.TRUE.equals(each)) {
                        yield true;
                    }
                    unsettled |= each == null;
                }
                yield unsettled ? null : false;
            }
            case LawProposition.Compared<DeclaredArgument> compared ->
                    holds(compared.form(), compared.states(), container, size);
            case LawProposition.Observed<DeclaredArgument> _,
                 LawProposition.SomeElement<DeclaredArgument> _,
                 LawProposition.Same<DeclaredArgument> _,
                 LawProposition.Inside<DeclaredArgument> _ -> null;
        };
    }

    /** Whether {@code form} stands to nought as {@code states}, each number of it settled by the
     *  size, or null where one is not. */
    private static Boolean holds(LinearForm<LawNumber<DeclaredArgument>> form,
                                 Rel states, int container, int size) {
        ExactRatio total = form.constant();
        for (Map.Entry<LawNumber<DeclaredArgument>, ExactRatio> each : form.coefs().entrySet()) {
            ExactRatio number = numberOf(each.getKey(), container, size);
            if (number == null || !(number.times(each.getValue())
                    .flatMap(total::plus) instanceof ExactAnswer.Held<ExactRatio>(ExactRatio sum))) {
                return null;
            }
            total = sum;
        }
        return states.holds(total.signum());
    }

    /** What {@code number} comes to where the container holds {@code size} elements, or null where
     *  the size does not settle it. */
    private static ExactRatio numberOf(LawNumber<DeclaredArgument> number, int container,
                                       int size) {
        return switch (number) {
            case LawNumber.SizeOf<DeclaredArgument>(
                    LawSubject.Argument<DeclaredArgument>(DeclaredArgument of))
                    when of.position() == container -> ExactRatio.of(size);
            case LawNumber.HowManyDifferent<DeclaredArgument> different
                    when different.container().position() == container -> ExactRatio.of(size);
            // Over no elements, whatever is asked of each comes to nothing.
            case LawNumber.SumOver<DeclaredArgument> sum
                    when sum.container().position() == container && size == 0 -> ExactRatio.ZERO;
            case LawNumber.HowManyMeet<DeclaredArgument> meet
                    when meet.container().position() == container && size == 0 -> ExactRatio.ZERO;
            case LawNumber.SizeOf<DeclaredArgument> _,
                 LawNumber.HowManyDifferent<DeclaredArgument> _,
                 LawNumber.SumOver<DeclaredArgument> _,
                 LawNumber.HowManyMeet<DeclaredArgument> _,
                 LawNumber.AnArgument<DeclaredArgument> _,
                 LawNumber.CodePointsOf<DeclaredArgument> _ -> null;
        };
    }
}
