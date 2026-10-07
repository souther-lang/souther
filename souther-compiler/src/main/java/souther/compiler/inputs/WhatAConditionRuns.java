package souther.compiler.inputs;

import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.core.Evaluated;

import java.util.ArrayList;
import java.util.List;

/**
 * What every run that brought a condition out one way ran on the way.
 *
 * <p>Read off the one account of what runs when ({@link Evaluated}). An operator that stops when
 * its answer is settled runs its left always, and its right only where the left came out a way. Where
 * the operator came out that same way, both came out that way — {@code &&} holding is both holding,
 * {@code ||} failing is both failing. Otherwise the left came out one of two ways and which is not
 * known here, so only that it ran is.
 *
 * <p>Read through what a truth is asked of ({@link InputTruth#asked}) at every step and not only at
 * the top: a condition given a name, a part of one given a name, and one denied are the condition
 * they stand for. A reading that looked for the operators as the condition is written would find
 * none behind a name, and a condition named would come out a different decision from the same
 * condition written out.
 *
 * <p>One reading for the readers that ask it: which operators a run down an arm is known to have
 * run, and which parts it is known to have brought out which way.
 *
 * @param mayNotRun the operands that run only on some runs, of the operators every such run ran:
 *                  outermost first, as the expressions they are
 * @param settled   the parts that are not such operators and that every such run brought out a
 *                  known way, in the order they are written
 * @param whole     whether every part the condition is made of is among {@code settled}: false where
 *                  one stands under an operator whose way out is not known
 */
public record WhatAConditionRuns(List<Core> mayNotRun, List<Settled> settled, boolean whole) {

    public WhatAConditionRuns {
        mayNotRun = List.copyOf(mayNotRun);
        settled = List.copyOf(settled);
    }

    /**
     * A part that came out {@code held}, as what it is asked of.
     *
     * @param reads what the names in it read, which is where it was written and not where the
     *              condition was asked
     */
    public record Settled(Core part, boolean held, InputReads reads) { }

    /** What every run that brought {@code cond}, read under {@code reads}, out {@code cameOut}
     *  ran. */
    public static WhatAConditionRuns whenItCameOut(Core cond, boolean cameOut, InputReads reads,
                                                   Symbols symbols,
                                                   DeclarationNewtypes newtypes) {
        Walk walk = new Walk(symbols, newtypes);
        walk.known(cond, cameOut, reads);
        return new WhatAConditionRuns(walk.mayNotRun, walk.settled, walk.whole);
    }

    /** The step of {@code e} that runs only on some runs, or null where every part of it runs
     *  whenever it does. */
    private static Evaluated.Step.OnlyWhere onlySometimes(Core e) {
        for (Evaluated.Step each : Evaluated.inOrder(Core.withoutStanding(e))) {
            if (each instanceof Evaluated.Step.OnlyWhere some) {
                return some;
            }
        }
        return null;
    }

    private static final class Walk {

        private final Symbols symbols;
        private final DeclarationNewtypes newtypes;
        private final List<Core> mayNotRun = new ArrayList<>();
        private final List<Settled> settled = new ArrayList<>();
        private boolean whole = true;

        Walk(Symbols symbols, DeclarationNewtypes newtypes) {
            this.symbols = symbols;
            this.newtypes = newtypes;
        }

        /** {@code e}, which came out {@code held}. */
        void known(Core e, boolean held, InputReads reads) {
            InputTruth.Asked asked = InputTruth.asked(e, held, reads, symbols, newtypes);
            Evaluated.Step.OnlyWhere some = onlySometimes(asked.value());
            if (some == null) {
                settled.add(new Settled(asked.value(), asked.holding(), asked.reads()));
                return;
            }
            mayNotRun.add(some.expression());
            if (asked.holding() == some.comesOut()) {
                known(some.asked(), asked.holding(), asked.reads());
                known(some.expression(), asked.holding(), asked.reads());
            } else {
                unknown(some.asked(), asked.reads());
                // The right may not have run, and where it did, which way is not known either.
                whole = false;
            }
        }

        /** {@code e}, which ran and came out a way not known here. */
        void unknown(Core e, InputReads reads) {
            whole = false;
            // Which way is asked makes no difference to what is looked through, only to which way
            // a denial turns it, and that is not known here either.
            InputTruth.Asked asked = InputTruth.asked(e, true, reads, symbols, newtypes);
            Evaluated.Step.OnlyWhere some = onlySometimes(asked.value());
            if (some != null) {
                mayNotRun.add(some.expression());
                unknown(some.asked(), asked.reads());
            }
        }
    }
}
