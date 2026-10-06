package souther.compiler.partition;

import souther.compiler.check.BooleanMeaning;
import souther.compiler.core.Core;
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
 */
interface WhatNamesStandFor {

    /** What {@code e} stands for, through every name that is one value; itself where it is none. */
    Core denotes(Core e);

    /** Whether {@code e} is a value the source wrote out all the way down, its names read here. */
    boolean writtenOut(Core e);

    /**
     * What every row brings {@code comparison} out as, where its two sides differ by the same
     * amount on all of them — or empty where it is no comparison, or one whose answer turns on the
     * row.
     */
    Optional<Boolean> everyRowBrings(Core comparison);

    static WhatNamesStandFor in(InputReads reads, InputReading read) {
        return new WhatNamesStandFor() {
            @Override
            public Core denotes(Core e) {
                return reads.denotes(e, read.rules().symbols(), read.rules().newtypes()).value();
            }

            @Override
            public boolean writtenOut(Core e) {
                return reads.writtenOut(e, read.rules().symbols(), read.rules().newtypes());
            }

            @Override
            public Optional<Boolean> everyRowBrings(Core comparison) {
                return BooleanMeaning.asAComparison(comparison).flatMap(one ->
                        AffineReading.read(one.stated(), read.domain(), reads, read.rules())
                                instanceof AffineReading.OfAComparison.CutsNothing constant
                                ? Optional.of(constant.holds(
                                        one.stated().claim().statedRelation()))
                                : Optional.empty());
            }
        };
    }
}
