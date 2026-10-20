package souther.compiler.partition;

import java.util.List;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Hir;
import souther.compiler.check.Carrier;
import souther.compiler.check.NewtypeInners;
import souther.compiler.check.NumberAt;
import souther.compiler.check.ReadingPolicy;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.ScopedDeclarations;
import souther.compiler.check.Symbols;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.observe.ObservedValue;
import souther.compiler.semantics.CaseMapping;
import souther.compiler.semantics.CodePointClass;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;
import souther.compiler.values.AsACompilationAllows;
import souther.runtime.Strings;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the code points of a string come to is a number of its own at the string's position, and
 * the two directions of it — reading a row, writing a value — are held to each other and to the
 * run time's own list of code points.
 *
 * <p>The oracle is written here, as the numbers each string's code points are, and not read from
 * the code that adds them: a reader and a writer that both added the same wrong thing agree with
 * each other at every string either offers.
 */
class WhatTheCodePointsOfAStringComeToIsReadAndWrittenAsTheRunTimeAddsThemTest {

    private static final Symbols SYMBOLS = Symbols.none(DefaultStdlib.get());
    private static final RuleReadingSource RULES = RuleReadings.ofNoClauseFiled(SYMBOLS);
    private static final ReadingPolicy POLICY = new ReadingPolicy(64, 12,
            AsACompilationAllows.admittedValues(), AsACompilationAllows.whatARuleLeaves());
    private static final RuleReadingContext READING = RuleReadingContext.unshared(RULES, POLICY);
    private static final NewtypeInners INNERS = ScopedDeclarations.wrapsOf(SYMBOLS);
    private static final TermPath AT = TermPath.of("t");

    private static NumericTerm.CodePointValueSum summed(TermPath at) {
        NumericTerm.CodePointValueSum made =
                NumericTerm.CodePointValueSum.of(at, Type.STRING, INNERS);
        assertNotNull(made, "a string's code points are added up");
        return made;
    }

    private static TermOrders orders() {
        return TermOrdersFixtures.at(summed(AT), Type.STRING, SYMBOLS);
    }

    /** Only a string has code points to add up. */
    @Test
    void onlyAStringHasCodePointsToAddUp() {
        assertNull(NumericTerm.CodePointValueSum.of(AT, Type.INT, INNERS));
        assertNull(NumericTerm.CodePointValueSum.of(AT, new Type.ListOf(Type.INT), INNERS));
    }

    /**
     * One term per place, and another term than every other number of the same string: how long it
     * is, how many of its code points are in a class, and what a total of a container standing
     * there would be.
     */
    @Test
    void theSumIsNamedByThePlaceAndIsNoOtherNumberOfIt() {
        assertEquals(summed(AT), summed(TermPath.of("t")));
        assertNotEquals(summed(AT), summed(TermPath.of("u")));
        assertEquals(TermPath.of("t").then("name"),
                summed(AT).movedTo(path -> path.then("name")).position());

        NumericTerm length = NumericTerm.TakenOf.asItStands(
                ValueName.Stdlib.operation("String", "length"), AT, Type.STRING, INNERS, SYMBOLS);
        assertNotEquals(length, summed(AT));
        assertNotEquals(NumericTerm.CodePointClassCount.of(AT, new CodePointClass.NotWhitespace(),
                CaseMapping.NONE, Type.STRING, INNERS), summed(AT));
        assertNotEquals(NumberAt.takenAsItStands(AT, ValueName.Stdlib.operation("List", "sum")),
                NumberAt.codePointSumOf(AT));
    }

    /** Never below nought, and a whole number read off a string. */
    @Test
    void theSumIsAWholeNumberFromNought() {
        assertTrue(summed(AT).intrinsicBounds().admits(Count.of(0)));
        assertFalse(summed(AT).intrinsicBounds().admits(Count.of(-1)));
        assertEquals(Carrier.WHOLE, orders().answered());
        assertEquals(Carrier.TEXT, orders().observed());
    }

    /**
     * What each string's code points come to, in strings chosen to tell scalar values from UTF-16
     * units: a character past the first plane is one code point and two units, and enough of them
     * come to more than an {@code int} holds, which the language's whole numbers hold.
     */
    @Test
    void whatTheCodePointsComeToIsWhatTheRunTimeListsOfTheString() {
        String grinning = "😀";
        Object[][] expected = {
            {"", 0L},
            {"A", 65L},
            {"AB", 131L},
            {" ", 32L},
            {grinning, 128_512L},
            {"a" + grinning, 128_609L},
            {grinning.repeat(17_000), 2_184_704_000L},
        };
        for (Object[] row : expected) {
            String text = (String) row[0];
            assertEquals(new NumericTerm.Reading.Number(Count.of((long) row[1])),
                    orders().read(new ObservedValue.Text(text)),
                    () -> "what the code points of a string " + text.length() + " units long"
                            + " come to");
        }
    }

    /**
     * And what is read is what {@code List.sum} answers of the list {@code String.codePoints}
     * answers on a run, over the string as the language holds it: none at all, ASCII, one past
     * the first plane, and a letter with a combining mark the language composes into one.
     */
    @Test
    void whatIsReadIsTheTotalOfTheListTheRunTimeAnswers() {
        for (String written : List.of("", "AB", "a😀b", "é", "é")) {
            String held = Strings.admit(written);
            long total = Strings.codePoints(held).stream().mapToLong(Long::longValue).sum();
            assertEquals(new NumericTerm.Reading.Number(Count.of(total)),
                    orders().read(new ObservedValue.Text(held)),
                    () -> "the code points of " + held.codePoints().boxed().toList());
        }
    }

    /** Only a string is read, and anything else holds no number of this kind. */
    @Test
    void whatIsNotAStringHoldsNoSum() {
        assertInstanceOf(NumericTerm.Reading.NotNumber.class,
                orders().read(new ObservedValue.Integer(3)));
    }

    /**
     * What is built for a sum reads back as that sum, as the language holds the text: small sums
     * that only control characters reach, the code point of a letter, one past the first plane,
     * more than one code point holds, and what only as many code points as a string is searched
     * for in full reach together.
     */
    @Test
    void everyStringBuiltForASumReadsBackAsIt() {
        int checked = 0;
        long most = CompositionBudget.CODE_POINTS_A_STRING_IS_SEARCHED_IN_FULL.maximum();
        for (long each : new long[] {0, 1, 9, 10, 65, 200, 128_512, 2L * Character.MAX_CODE_POINT,
                5L * Character.MAX_CODE_POINT + 7, most * Character.MAX_CODE_POINT}) {
            TermRealizations.Realization.Built built = assertInstanceOf(
                    TermRealizations.Realization.Built.class,
                    TermRealizations.at(Type.STRING, orders(), Count.of(each),
                            NothingTheRulesSay.REGION, READING),
                    "some string's code points come to " + each);
            for (FixtureTemplate value : built.values()) {
                String offered = ((Hir.StringLit) value.value()).value();
                assertEquals(Strings.admit(offered), offered, "offered as held");
                assertEquals(new NumericTerm.Reading.Number(Count.of(each)),
                        orders().read(new ObservedValue.Text(offered)), "built for " + each);
                checked++;
            }
        }
        assertTrue(checked > 0, "nothing was built, so nothing was read back");
    }
}
