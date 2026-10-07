package souther.compiler.flow;

import souther.compiler.core.Core;

import java.util.ArrayList;
import java.util.List;

/**
 * What every run that brought a condition out one way ran on the way, read off how the condition
 * is written.
 *
 * <p>An operator that stops when its answer is settled always runs its left. It runs its right too
 * where it came out the way that needs both — {@code &&} holding, {@code ||} failing — and then both
 * came out that way. Otherwise the left came out one of two ways and which is not known here, so
 * only that it ran is.
 *
 * <p>One reading for the readers that ask it: which operators a run down an arm is known to have
 * run, and which parts it is known to have brought out which way. Two readers working this out
 * apart would part over an operator one of them learned to see through.
 *
 * @param operators the operators that stop when their answer is settled and that every such run
 *                  ran, outermost first
 * @param settled   the parts that are not such operators and that every such run brought out a
 *                  known way, in the order they are written
 * @param whole     whether every part the condition is made of is among {@code settled}: false where
 *                  one stands under an operator whose way out is not known
 */
public record WhatAConditionRuns(List<Core.Binary> operators, List<Settled> settled,
                                 boolean whole) {

    public WhatAConditionRuns {
        operators = List.copyOf(operators);
        settled = List.copyOf(settled);
    }

    /** A part that came out {@code held}. */
    public record Settled(Core part, boolean held) { }

    /** What every run that brought {@code cond} out {@code cameOut} ran. */
    public static WhatAConditionRuns whenItCameOut(Core cond, boolean cameOut) {
        Walk walk = new Walk();
        walk.known(cond, cameOut);
        return new WhatAConditionRuns(walk.operators, walk.settled, walk.whole);
    }

    private static final class Walk {

        private final List<Core.Binary> operators = new ArrayList<>();
        private final List<Settled> settled = new ArrayList<>();
        private boolean whole = true;

        /** {@code e}, which came out {@code held}. */
        void known(Core e, boolean held) {
            if (!(Core.withoutStanding(e) instanceof Core.Binary binary)
                    || !binary.op().stopsWhenItsAnswerIsSettled()) {
                settled.add(new Settled(e, held));
                return;
            }
            operators.add(binary);
            if (held == binary.op().rightRunsWhenLeftIs()) {
                known(binary.left(), held);
                known(binary.right(), held);
            } else {
                unknown(binary.left());
                // The right may not have run, and where it did, which way is not known either.
                whole = false;
            }
        }

        /** {@code e}, which ran and came out a way not known here. */
        void unknown(Core e) {
            whole = false;
            if (Core.withoutStanding(e) instanceof Core.Binary binary
                    && binary.op().stopsWhenItsAnswerIsSettled()) {
                operators.add(binary);
                unknown(binary.left());
            }
        }
    }
}
