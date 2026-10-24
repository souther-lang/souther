package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.core.Kernel;
import souther.compiler.types.BindingId;
import souther.compiler.types.ValueName;

/**
 * What an option holds where it holds a value, followed through the operations that made it.
 *
 * <p>One walk for every reader that asks it, whatever it reads names in. The reading of an input
 * names an arm's payload with the answer and the discharge of a rule hands it to the arm as its
 * value, and two walks would be a program measured as {@code c - 48} and checked as {@code c} less
 * some number the first time one of them learned an operation the other did not.
 *
 * <p>What is decided here is how an option was made: a lookup in a list written out holds the
 * element its index picks ({@link ElementsWrittenOut#picked}), and an operation answering its
 * closure on what another option holds ({@link BoundOperationFacts#answersTheClosureOnWhatItHolds})
 * holds the closure's body read with its parameter standing for what the other holds — worked out
 * by this same walk. Every other option is the reader's to answer ({@link Reading#otherwise}): what
 * stands at a position of an input, what a lookup in an input's map answered, and the element an
 * index picks of a list made of an input are places only the reading of an input has.
 *
 * <p>Each step goes into an argument of the call before it, and each call is found through the
 * names it was bound to, so the descent ends where the tree does.
 */
public final class WhatAnOptionHolds {

    private WhatAnOptionHolds() {
    }

    /**
     * What a walk asks of a reader: how names are followed in its environment {@code E}, and its
     * own answer {@code H} to what an option holds.
     *
     * @param <E> the environment
     * @param <H> the reader's answer
     */
    public interface Reading<E, H> extends ElementsWrittenOut.Reading<E> {

        /** What the option holds where it is the element a lookup in a list written out picks. */
        H anElement(ElementsWrittenOut.Stood<E> element);

        /** What the option holds where a closure answered {@code answered} on what another option
         *  holds, which is {@code handed}. */
        H madeByAClosure(ElementsWrittenOut.Stood<E> answered, H handed);

        /** {@code at} with {@code parameter} standing for {@code handed}, as a closure handed what an
         *  option holds is read. */
        E holding(E at, BindingId parameter, H handed);

        /**
         * What {@code option}, followed through its names, holds where no operation this follows
         * made it.
         *
         * @param applied the operation {@code option} applies, or null where it applies none
         */
        H otherwise(ElementsWrittenOut.Stood<E> option, AnOperationApplied applied);

        /** Nothing says. */
        H unsaid();
    }

    /** What {@code option}, read in {@code at}, holds where it holds a value. */
    public static <E, H> H of(Core option, E at, Reading<E, H> reading) {
        ElementsWrittenOut.Stood<E> looked = reading.standing(option, at);
        AnOperationApplied applied = AnOperationApplied.of(Core.withoutStanding(looked.value()));
        if (applied == null) {
            return reading.otherwise(looked, null);
        }
        if (applied.operation() instanceof ValueName.Stdlib.Operation listed
                && reading.symbols().kernelOf(listed) == Kernel.LIST_GET) {
            ElementsWrittenOut.Occurrence<E> picked =
                    ElementsWrittenOut.picked(looked.value(), looked.at(), reading);
            return picked == null ? reading.otherwise(looked, applied)
                    : reading.anElement(picked.value());
        }
        BoundOperationFacts.ClosureOnWhatItHolds made =
                DefaultBoundOperationFacts.get().answersTheClosureOnWhatItHolds(applied.operation());
        if (made == null) {
            return reading.otherwise(looked, applied);
        }
        int held = CallArguments.positionOf(made.option(), applied.operation());
        int closure = CallArguments.positionOf(made.closure(), applied.operation());
        if (held < 0 || held >= applied.args().size() || closure < 0
                || closure >= applied.args().size()) {
            return reading.unsaid();
        }
        // The closure is read where it stands, and may be a name for one; only a closure written as
        // a block of one parameter is read.
        ElementsWrittenOut.Stood<E> step = reading.standing(applied.args().get(closure),
                looked.at());
        if (!(Core.withoutStanding(step.value()) instanceof Core.Block block)
                || block.params().size() != 1 || block.params().getFirst() == null
                || block.params().getFirst().binding() == null) {
            return reading.unsaid();
        }
        H handed = of(applied.args().get(held), looked.at(), reading);
        return reading.madeByAClosure(new ElementsWrittenOut.Stood<>(block.body(),
                reading.holding(step.at(), block.params().getFirst().binding(), handed)), handed);
    }
}
