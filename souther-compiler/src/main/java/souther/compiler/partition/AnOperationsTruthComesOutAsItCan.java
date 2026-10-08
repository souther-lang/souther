package souther.compiler.partition;

import souther.compiler.check.AnOperationApplied;
import souther.compiler.check.ScopeStep;
import souther.compiler.core.Core;
import souther.compiler.flow.ComparisonWays;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

import java.util.Set;
import java.util.function.Function;
import java.util.function.Predicate;

/**
 * The ways a value comes out in a tree where the language's operations stand, with a truth one of
 * them answers coming out each way it can.
 *
 * <p>The tree's own reading answers for comparisons and for a truth at a position, and an
 * operation's answer is a value it cannot witness. Left there, a condition written
 * {@code a > 0 || List.isEmpty(xs)} was one way through and not three: the second part arrived as a
 * value nothing named, and the rules a body draws by it were the fork's two arms with nothing in
 * between.
 *
 * <p>Asked one way at a time, as {@link ComparisonWays} asks: whether some value brings the truth
 * out {@code want}. That is a question about which answers the truth can give and not about whether
 * it varies, so it is answered with which ones those are ({@link TruthOutcomes}) — a truth fixed at
 * false is passed the way it comes out, and one this reading cannot name is stood behind neither
 * way.
 *
 * <p>And a value the source settles comes out the one way it does, whatever the tree's own reading
 * would stand behind. A comparison whose sides differ by the same amount on every row is one the
 * tree reads as coming out either way, and a way past it the other way is a way no row takes —
 * which is what {@link DemandReading} says of it too, from the same answer.
 */
final class AnOperationsTruthComesOutAsItCan implements ComparisonWays {

    private final InputReads reads;
    private final InputReading read;

    AnOperationsTruthComesOutAsItCan(InputReads reads, InputReading read) {
        this.reads = reads;
        this.read = read;
    }

    @Override
    public boolean comesOut(Core e, boolean want, Function<Core.Read, Core> settledBy) {
        TruthOutcomes.Outcomes outcomes = TruthOutcomes.ofTheTruth(e,
                WhatNamesStandFor.in(reads, read));
        if (outcomes.always(true) || outcomes.always(false)) {
            return outcomes.allows(want);
        }
        if (ComparisonWays.OF_THE_TREE.comesOut(e, want, settledBy)) {
            return true;
        }
        return AnOperationApplied.of(e) != null
                && Core.withoutStanding(e).type() == Type.Prim.BOOL
                && outcomes.allows(want);
    }

    @Override
    public Predicate<Core.Case> mayTake(Core.Match match) {
        Set<TypeSymbol> written = reads.casesWritten(match.scrutinee(), read.rules().symbols(),
                read.rules().newtypes());
        return written == null ? arm -> true
                : arm -> InputReads.whetherEveryRowTakes(arm, written).orElse(true);
    }

    @Override
    public ComparisonWays entering(ScopeStep step) {
        InputReads inside = reads.entering(step, read.rules().symbols(), read.rules().newtypes());
        return inside == reads ? this : new AnOperationsTruthComesOutAsItCan(inside, read);
    }
}
