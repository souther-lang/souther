package souther.compiler.partition;

import souther.compiler.check.BooleanMeaning;
import souther.compiler.check.ScopeStep;
import souther.compiler.core.Core;
import souther.compiler.inputs.Denotation;
import souther.compiler.inputs.InputReading;
import souther.compiler.inputs.InputReads;

import java.util.Optional;

/**
 * What the values a truth reads stand for, as the reading of the input says — the questions a
 * reading of which answers a truth can give asks of it.
 *
 * <p>All of them and not only the first. Handed the expression a name denotes and nothing else, a
 * reader of a closure walked into it without knowing what the closure is handed: a parameter given
 * the elements of a list written out is one of written values, which the reading of the input
 * knows ({@code ReadMeaning.OneOf}) and an expression cannot say. And a comparison whose two sides
 * differ by the same amount on every row comes out one way for all of them, which the arithmetic
 * that reads it knows ({@link AffineReading.OfAComparison.CutsNothing}) and the tree does not.
 * Readers that answered these for themselves answered them in as many places as there were
 * readers, and the way a body is walked and what a way past a condition asks of a row came apart
 * over a predicate the source settles.
 *
 * <p><b>Read where they stand.</b> The answers are about one reading of the body, and a walk that
 * goes on into a {@code let}, an arm or a closure has gone where names are bound that the reading
 * it started in does not hold: a helper expanded inside a closure binds its own parameters there.
 * So a walk steps these with it ({@link #entering}), and what a name denotes comes back with the
 * reading it stands in ({@link #denotes}) — an expression handed on without it is asked about in a
 * reading it is not in, and a field of the helper's parameter is a position the outer reading
 * cannot name.
 */
interface WhatNamesStandFor {

    /** The reading these names are read in. */
    InputReads reads();

    /** What {@code e} stands for, through every name that is one value, and the reading it stands
     *  in there; itself, here, where it is none. */
    Denotation denotes(Core e);

    /** What {@code e} stands as, through every name that is one value and every binding whose body
     *  is the value, and the reading it stands in there. */
    Denotation standing(Core e);

    /** The same questions asked in {@code reads}, where a denotation went. */
    WhatNamesStandFor in(InputReads reads);

    /** The same questions asked one step down, through {@code step}. */
    WhatNamesStandFor entering(ScopeStep step);

    /** Whether {@code e} is a value the source wrote out all the way down, its names read here. */
    boolean writtenOut(Core e);

    /**
     * What every row brings {@code comparison} out as, where its two sides differ by the same
     * amount on all of them — or empty where it is no comparison, or one whose answer turns on the
     * row.
     */
    Optional<Boolean> everyRowBrings(Core comparison);

    static WhatNamesStandFor in(InputReads reads, InputReading read) {
        return new In(reads, read);
    }

    /**
     * The answers the reading of the input gives, with the names as {@code reads} has them.
     *
     * <p>Moved along a walk as the environment is ({@link #entering}), and so asking nothing of the
     * input's domain itself: the arithmetic that reads a comparison against it is handed
     * {@code read} and asks there.
     */
    record In(InputReads reads, InputReading read) implements WhatNamesStandFor {

        @Override
        public Denotation denotes(Core e) {
            return reads.denotes(e, read.rules().symbols(), read.rules().newtypes());
        }

        @Override
        public Denotation standing(Core e) {
            return reads.standing(e, read.rules().symbols(), read.rules().newtypes());
        }

        @Override
        public WhatNamesStandFor in(InputReads other) {
            return other == reads ? this : new In(other, read);
        }

        @Override
        public WhatNamesStandFor entering(ScopeStep step) {
            return in(reads.entering(step, read.rules().symbols(), read.rules().newtypes()));
        }

        @Override
        public boolean writtenOut(Core e) {
            return reads.writtenOut(e, read.rules().symbols(), read.rules().newtypes());
        }

        @Override
        public Optional<Boolean> everyRowBrings(Core comparison) {
            return BooleanMeaning.asAComparison(comparison).flatMap(one ->
                    AffineReading.read(one, reads, read)
                            instanceof AffineReading.OfAComparison.CutsNothing constant
                            ? Optional.of(constant.holds(one.claim().statedRelation()))
                            : Optional.empty());
        }
    }
}
