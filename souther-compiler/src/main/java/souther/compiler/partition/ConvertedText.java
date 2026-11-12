package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.meaning.DecisionAtom;
import souther.compiler.meaning.Quantity;
import souther.compiler.semantics.CaseMapping;
import souther.compiler.types.ValueName;

import java.util.List;

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
     * What {@code quantity} is made of by case conversions alone: what the first of them was
     * handed, and what they make of it.
     *
     * @param from    what the first conversion was handed, or {@code quantity} where it is made
     *                of none
     * @param through the conversions
     */
    record Conversion(Quantity from, CaseMapping through) {
    }

    /**
     * What {@code quantity} is made of by case conversions of one string, or null where it is made
     * by a call of anything else. The one place that goes down such a chain of calls, in a loop
     * ({@link Quantity.WhatAnOperationAnswers#chainOfOneArgument}).
     */
    static Conversion conversionOf(Quantity quantity) {
        Quantity from = quantity;
        List<ValueName.Stdlib> operations = List.of();
        if (quantity instanceof Quantity.WhatAnOperationAnswers answers) {
            Quantity.WhatAnOperationAnswers.OfOneArgument chain = answers.chainOfOneArgument();
            from = chain.from();
            operations = chain.operations();
        }
        CaseMapping through = CaseMapping.NONE;
        for (ValueName.Stdlib operation : operations) {
            through = CaseMapping.applying(operation, through);
            if (through == null) {
                return null;
            }
        }
        return new Conversion(from, through);
    }

    /**
     * The text {@code quantity} is, where it is a string of the input or one made of it by case
     * conversions of one string — or null where it is made by anything else.
     */
    static ConvertedText of(Quantity quantity) {
        Conversion made = conversionOf(quantity);
        return made != null
                && made.from() instanceof DecisionAtom.OfTheInput(NumericTerm.ValueOf place, var _)
                ? new ConvertedText(place, made.through()) : null;
    }

    /** The text spelled round {@code path}, as a model writes it. */
    String writtenAround(String path) {
        return through.writtenAround(path);
    }
}
