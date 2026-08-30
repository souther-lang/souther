package souther.compiler.observe;

import souther.compiler.types.ValueName;

import java.util.List;

/**
 * What one {@code example} row states, as something that did not read the source can hold it.
 *
 * <p>A row states what a behavior owes for an input, and running it is not what settles that: the
 * inputs and the expectation are written down, bound and checked whether or not anything applies
 * the behavior. So what a row states is a fact about the model, and this is that fact taken once —
 * where the row was read — rather than a source text something else would have to read again.
 *
 * <p>Three arms, because a row that cannot be handed over as values must not arrive as no row. A
 * reader given nothing for it would count a row it never saw among the rows it walked and found
 * empty, and report a behavior as having nothing to say about an input someone wrote down.
 *
 * <p>What it is not: running the row. Nothing here applies anything, and what a reader does with a
 * row it was given is the reader's.
 */
public sealed interface RowStatement {

    /**
     * The inputs the row hands over and what it states of the answer.
     *
     * <p>Every value here is whole. A row whose input or expectation could not be held in full is
     * {@link Incomplete}, never this — so a reader that has one of these has the values the row was
     * written with and not as much of them as fit.
     */
    record Stated(List<ObservedValue> inputs, Expectation expects) implements RowStatement {

        public Stated {
            inputs = List.copyOf(inputs);
            if (expects == null) {
                throw new IllegalArgumentException("a row states something of the answer");
            }
            // Both halves, and whole rather than small enough: how much of a value may be kept
            // somewhere is a limit's to say and is applied where a statement is made, while what
            // this refuses is a value that is not all there — which no reader of one could be given
            // anything true about.
            for (ObservedValue input : inputs) {
                if (!Limits.UNBOUNDED.admits(input)) {
                    throw new IllegalArgumentException("a stated row's values are there in full;"
                            + " a row holding one that is not is Incomplete");
                }
            }
            if (expects instanceof Expectation.TheValue(Asserted value)
                    && !Limits.UNBOUNDED.admits(value)) {
                throw new IllegalArgumentException("a stated row's expectation is there in full;"
                        + " a row holding one that is not is Incomplete");
            }
        }
    }

    /**
     * The behavior takes something injected, so the row states more than values.
     *
     * <p>A row runs against a bound implementation, and where the behavior depends on something
     * injected, what stands in for that dependency is the rest of what makes the row runnable.
     * Handing over the inputs and the expectation alone would not be handing over the row: a reader
     * whose dependency is an import has nothing to answer that import with, and one that applied the
     * behavior anyway would be reporting what a run that cannot happen answered.
     *
     * <p>So the row crosses as itself and says what is missing. Which dependencies those are is what
     * the behavior requires, in the order it takes them.
     */
    record RequiresStandIns(List<ValueName.Behavior> dependencies) implements RowStatement {

        public RequiresStandIns {
            dependencies = List.copyOf(dependencies);
            if (dependencies.isEmpty()) {
                throw new IllegalArgumentException("a row that needs nothing stood in for states"
                        + " its values");
            }
        }
    }

    /**
     * A value the row states could not be held in full, and which one.
     *
     * <p>The first thing that stopped the row from being stated, in the order the row is read:
     * whether anything has to stand in, then the inputs as they were written, then the expectation.
     * So this says what the statement could not be made of and not everything that is wrong with the
     * row — a reader meeting one has been told the row states values it cannot be given, not that
     * everything else about it is fine.
     */
    record Incomplete(Side side, Incompleteness.Code why) implements RowStatement {

        public Incomplete {
            if (side == null || why == null) {
                throw new IllegalArgumentException("a row that states no values says what and why");
            }
            // The two are one fact read two ways, so they are held to each other where they are
            // written: a value stops for a reason a value stops for, and a reading that did not
            // finish stopped for the one reason a reading stops for. Kept apart, a reader would meet
            // a value that ran out of time and a reading that was too large to keep.
            boolean aValue = side instanceof Side.AnInput || side instanceof Side.TheExpectation;
            boolean stopped = why == Incompleteness.Code.VALUE_TRUNCATED
                    || why == Incompleteness.Code.VALUE_UNREADABLE;
            if (aValue != stopped) {
                throw new IllegalArgumentException(side + " does not stop for " + why);
            }
        }
    }

    /** What a row states that could not be held. */
    sealed interface Side {

        /** The input at {@code at}, counted from zero, in the order the behavior takes them. */
        record AnInput(int at) implements Side {

            public AnInput {
                if (at < 0) {
                    throw new IllegalArgumentException("an input stands at zero or later: " + at);
                }
            }
        }

        /** What the row states of the answer. */
        record TheExpectation() implements Side {}

        /**
         * Not one of the row's values: this compile did not finish reading them.
         *
         * <p>A row whose evaluation ran out of time or spent its budget was written and states what
         * it states; what is missing is the reading of it, and a reader told that one of its values
         * was too large would have been told something about the model that nobody established.
         */
        record TheReading() implements Side {}
    }
}
