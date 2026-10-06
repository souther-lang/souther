package souther.compiler.partition;

import souther.compiler.check.DeclarationNewtypes;
import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.inputs.InputReads;

/**
 * What the names a value reads stand for, as the reading of the input says — the two questions a
 * reading of which answers a truth can give asks of it.
 *
 * <p>Both of them and not only the first. Handed the expression a name denotes and nothing else, a
 * reader of a closure walked into it without knowing what the closure is handed: a parameter given
 * the elements of a list written out is one of written values, which the reading of the input
 * knows ({@code ReadMeaning.OneOf}) and an expression cannot say. Readers that answered it for
 * themselves answered it in as many places as there were readers, and one that knew it only for
 * the closure it happened to be in read the same name two ways.
 */
interface WhatNamesStandFor {

    /** What {@code e} stands for, through every name that is one value; itself where it is none. */
    Core denotes(Core e);

    /** Whether {@code e} is a value the source wrote out all the way down, its names read here. */
    boolean writtenOut(Core e);

    static WhatNamesStandFor in(InputReads reads, Symbols symbols, DeclarationNewtypes newtypes) {
        return new WhatNamesStandFor() {
            @Override
            public Core denotes(Core e) {
                return reads.denotes(e, symbols, newtypes).value();
            }

            @Override
            public boolean writtenOut(Core e) {
                return reads.writtenOut(e, symbols, newtypes);
            }
        };
    }
}
