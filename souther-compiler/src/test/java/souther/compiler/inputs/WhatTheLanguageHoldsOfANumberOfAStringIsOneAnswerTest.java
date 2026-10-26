package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.check.NewtypeInners;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Symbols;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.semantics.CaseMapping;
import souther.compiler.semantics.CodePointClass;
import souther.compiler.semantics.TakenArguments;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;
import souther.compiler.values.TextExtents;
import souther.runtime.Strings;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * What the language holds of a number of a string is one answer, asked by the numeric reading of a
 * form and by the proof that a string of a length can be written.
 *
 * <p>The longest string is the run time's, and the sum of what the code points of a string come to
 * is that many of the last one. A number nothing ends is ended by nothing, and a form is ended
 * where its terms are.
 */
class WhatTheLanguageHoldsOfANumberOfAStringIsOneAnswerTest {

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());
    private static final NewtypeInners INNERS = ScopedDeclarations.wrapsOf(SYMBOLS);
    private static final long LONGEST = Strings.LONGEST_TEXT;

    private static NumericTerm.TakenOf lengthAt(String name) {
        NumericTerm.TakenOf made = NumericTerm.TakenOf.of(
                ValueName.Stdlib.operation("String", "length"),
                ObservationSource.asItStands(TermPath.of(name)), TakenArguments.NONE, Type.STRING,
                INNERS, SYMBOLS);
        assertNotNull(made, "the length of a string is a number of it");
        return made;
    }

    private static NumericTerm.ValueOf valueAt(String name) {
        return new NumericTerm.ValueOf(TermPath.of(name));
    }

    private static NumericDomain.Bounds between(long least, long most) {
        return new NumericDomain.Bounds(Endpoint.inclusive(Count.of(least)),
                Endpoint.inclusive(Count.of(most)));
    }

    private static LinearForm<NumericTerm> form(Object... termsAndWeights) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        for (int i = 0; i < termsAndWeights.length; i += 2) {
            coefs.put((NumericTerm) termsAndWeights[i], (ExactRatio) termsAndWeights[i + 1]);
        }
        return new LinearForm<>(ExactRatio.ZERO, coefs);
    }

    @Test
    void theLongestStringIsTheRunTimes() {
        assertEquals(Strings.LONGEST_TEXT, TextExtents.LONGEST_STRING);
        assertEquals(LONGEST, RepresentationBounds.mostOf(lengthAt("s")));
    }

    @Test
    void aCountOfAClassAndASumOfCodePointsAreEndedWithTheLength() {
        NumericTerm count = NumericTerm.CodePointClassCount.of(TermPath.of("s"),
                new CodePointClass.NotWhitespace(), CaseMapping.NONE, Type.STRING, INNERS);
        NumericTerm sum = NumericTerm.CodePointValueSum.of(TermPath.of("s"), Type.STRING, INNERS);

        assertEquals(LONGEST, RepresentationBounds.mostOf(count));
        assertEquals(LONGEST * Character.MAX_CODE_POINT, RepresentationBounds.mostOf(sum));
    }

    @Test
    void aNumberNothingEndsIsEndedByNothing() {
        assertNull(RepresentationBounds.mostOf(valueAt("x")));
        assertEquals(NumericDomain.Bounds.OPEN, RepresentationBounds.of(valueAt("x")));
    }

    /** An operation of another type is not ended by the length of a string. */
    @Test
    void aYearIsEndedByTheCalendarAndNotByAString() {
        NumericTerm year = NumericTerm.TakenOf.of(ValueName.Stdlib.operation("Date", "year"),
                ObservationSource.asItStands(TermPath.of("d")), TakenArguments.NONE,
                Type.Prim.DATE, INNERS, SYMBOLS);

        assertNull(RepresentationBounds.mostOf(year));
    }

    @Test
    void aFormIsEndedWhereItsTermsAre() {
        ExactRatio one = ExactRatio.ONE;
        ExactRatio minusOne = one.negated();
        ExactRatio two = ExactRatio.of(2);

        assertEquals(between(0, 2 * LONGEST),
                RepresentationBounds.ofAForm(form(lengthAt("a"), one, lengthAt("b"), one)));
        assertEquals(between(-LONGEST, LONGEST),
                RepresentationBounds.ofAForm(form(lengthAt("a"), one, lengthAt("b"), minusOne)));
        assertEquals(between(0, 2 * LONGEST),
                RepresentationBounds.ofAForm(form(lengthAt("a"), two)));
        assertEquals(between(-2 * LONGEST, 0),
                RepresentationBounds.ofAForm(form(lengthAt("a"), two.negated())));
    }

    @Test
    void aFormOfNumbersNothingEndsSaysNothing() {
        assertEquals(NumericDomain.Bounds.OPEN, RepresentationBounds.ofAForm(
                form(valueAt("x"), ExactRatio.ONE, valueAt("y"), ExactRatio.ONE.negated())));
    }

    /** A term nothing ends leaves the side it decides open, and a side nothing decides is open. */
    @Test
    void aTermNothingEndsLeavesTheSideItDecidesOpen() {
        assertEquals(NumericDomain.Bounds.OPEN, RepresentationBounds.ofAForm(
                form(lengthAt("a"), ExactRatio.ONE, valueAt("x"), ExactRatio.ONE)));
    }

    /** A weight is any ratio: the ends are worked out exactly and rounded outward, so the run
     *  holds every value the form could. */
    @Test
    void aWeightThatIsNotWholeIsWorkedOutExactlyAndRoundedOutward() {
        ExactRatio half = ExactRatio.of(BigInteger.ONE, BigInteger.TWO);

        assertEquals(between(0, 402653183),
                RepresentationBounds.ofAForm(form(lengthAt("a"), half, lengthAt("b"),
                        ExactRatio.ONE)),
                "half the longest and the longest are one and a half of it: 402653182.5, up");
        assertEquals(between(-134217728, 0),
                RepresentationBounds.ofAForm(form(lengthAt("a"), half.negated())),
                "minus half the longest is -134217727.5, down");
    }
}
