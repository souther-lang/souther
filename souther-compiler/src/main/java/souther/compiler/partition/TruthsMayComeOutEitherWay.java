package souther.compiler.partition;

import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.ScopeStep;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.flow.ComparisonWays;
import souther.compiler.inputs.InputReads;
import souther.compiler.types.Type;

import java.util.function.Function;

/**
 * The ways a value comes out in a tree where the language's operations stand, with a truth one of
 * them answers coming out either way where its answer may be either.
 *
 * <p>The tree's own reading answers for comparisons and for a truth at a position, and an
 * operation's answer is a value it cannot witness. Left there, a condition written
 * {@code a > 0 || List.isEmpty(xs)} was one way through and not three: the second part arrived as a
 * value nothing named, and the rules a body draws by it were the fork's two arms with nothing in
 * between.
 *
 * <p>Either way only where the answer may vary ({@link WhatAForkTests#mayBeEither}). An operation
 * applied to what is written out answers the same every time, and a way through it the other way
 * round is a rule no row can take.
 */
final class TruthsMayComeOutEitherWay implements ComparisonWays {

    private final InputReads reads;
    private final Symbols symbols;
    private final DeclarationNewtypes newtypes;

    TruthsMayComeOutEitherWay(InputReads reads, Symbols symbols, DeclarationNewtypes newtypes) {
        this.reads = reads;
        this.symbols = symbols;
        this.newtypes = newtypes;
    }

    @Override
    public boolean comesOut(Core e, boolean want, Function<Core.Read, Core> settledBy) {
        if (ComparisonWays.OF_THE_TREE.comesOut(e, want, settledBy)) {
            return true;
        }
        return Core.withoutStanding(e) instanceof Core.PreservedCall applied
                && applied.type() == Type.Prim.BOOL
                && WhatAForkTests.mayBeEither(applied,
                        one -> reads.denotes(one, symbols, newtypes).value());
    }

    @Override
    public ComparisonWays entering(ScopeStep step) {
        InputReads inside = reads.entering(step, symbols, newtypes);
        return inside == reads ? this : new TruthsMayComeOutEitherWay(inside, symbols, newtypes);
    }
}
