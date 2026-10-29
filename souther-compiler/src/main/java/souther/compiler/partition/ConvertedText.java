package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Quantity;
import souther.compiler.semantics.CaseMapping;

/**
 * A string made of the string at a position of the input by case conversions, or that string
 * itself: the position, and what is done to the string at it.
 *
 * @param place   the position of the string of the input
 * @param through what the conversions make of it, none where it is the string itself
 */
record ConvertedText(NumericTerm.ValueOf place, CaseMapping through) {

    ConvertedText {
        if (place == null || through == null) {
            throw new IllegalArgumentException("a text is made of a position by conversions");
        }
    }

    /**
     * The text {@code quantity} is, where it is a string of the input or one made of it by case
     * conversions of one string — or null where it is made by anything else.
     */
    static ConvertedText of(Quantity quantity) {
        if (quantity instanceof DecisionAtom.OfTheInput(NumericTerm.ValueOf place)) {
            return new ConvertedText(place, CaseMapping.NONE);
        }
        if (quantity instanceof Quantity.WhatAnOperationAnswers answers
                && answers.of().size() == 1) {
            ConvertedText inner = of(answers.of().getFirst());
            CaseMapping mapping = inner == null ? null
                    : CaseMapping.applying(answers.operation(), inner.through());
            return mapping == null ? null : new ConvertedText(inner.place(), mapping);
        }
        return null;
    }

    /** The text spelled round {@code path}, as a model writes it. */
    String writtenAround(String path) {
        return through.writtenAround(path);
    }
}
