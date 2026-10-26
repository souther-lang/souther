package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.check.NewtypeInners;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.ObservationSource;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Towards;
import souther.compiler.semantics.CaseMapping;
import souther.compiler.semantics.CodePointClass;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;
import souther.runtime.Strings;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the language holds of a quantity is asked of the quantity, whichever of the three numbers
 * of a string it is on, and the answer says whether a value can stand at a level and on a side of
 * it.
 *
 * <p>A line on a count of the code points of a class is drawn only at the one the library's laws
 * name, and on what the code points of a string come to at what a body compares it with, so the
 * three numbers are held to the same answer here, one layer below the line a body draws.
 */
class WhatTheLanguageHoldsOfAQuantityIsAskedOfTheQuantityTest {

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());
    private static final NewtypeInners INNERS = ScopedDeclarations.wrapsOf(SYMBOLS);
    private static final TermPath AT = TermPath.of("s");
    private static final long LONGEST = Strings.LONGEST_TEXT;

    private static BorderQuantity on(NumericTerm term) {
        assertNotNull(term, "a number of a string");
        return new BorderQuantity.OfACoordinate("f", (NumericTerm.FromOnePosition) term,
                TermOrdersFixtures.at(term, Type.STRING, SYMBOLS));
    }

    private static Level level(long at) {
        return new Level.OfTheQuantity(ExactRatio.of(at));
    }

    private static void holdsUpTo(BorderQuantity quantity, long most) {
        HeldByTheLanguage held = quantity.heldByTheLanguage();

        assertTrue(held.admits(level(most)), "the most is a value");
        assertFalse(held.admits(level(most + 1)), "and nothing is past it");
        assertTrue(held.admits(level(0)), "and the floor is not the language's to refuse");
        assertTrue(held.holdsOnSide(level(most - 1), Towards.ABOVE, false),
                "a value stands above the one before the most");
        assertFalse(held.holdsOnSide(level(most), Towards.ABOVE, false),
                "and none above the most");
        assertTrue(held.holdsOnSide(level(most), Towards.ABOVE, true), "but the most is one");
    }

    @Test
    void aLengthIsHeldToTheLongestString() {
        NumericTerm length = NumericTerm.TakenOf.of(
                ValueName.Stdlib.operation("String", "length"),
                ObservationSource.asItStands(AT), TakenArguments.NONE, Type.STRING, INNERS,
                SYMBOLS);

        holdsUpTo(on(length), LONGEST);
    }

    @Test
    void aCountOfACodePointClassIsHeldToTheLongestString() {
        holdsUpTo(on(NumericTerm.CodePointClassCount.of(AT, new CodePointClass.NotWhitespace(),
                CaseMapping.NONE, Type.STRING, INNERS)), LONGEST);
    }

    @Test
    void whatTheCodePointsComeToIsHeldToTheLongestStringOfTheLastOne() {
        holdsUpTo(on(NumericTerm.CodePointValueSum.of(AT, Type.STRING, INNERS)),
                LONGEST * Character.MAX_CODE_POINT);
    }

    @Test
    void aRunNothingEndsIsHeldToNothing() {
        BorderQuantity value = on(new NumericTerm.ValueOf(AT));

        assertEquals(HeldByTheLanguage.NOWHERE, value.heldByTheLanguage());
    }
}
