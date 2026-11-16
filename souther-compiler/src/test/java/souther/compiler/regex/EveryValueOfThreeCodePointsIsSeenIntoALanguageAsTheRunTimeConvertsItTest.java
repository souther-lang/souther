package souther.compiler.regex;

import org.junit.jupiter.api.Test;

import souther.test.Nightly;

import java.util.List;

import static souther.compiler.regex.TheStringsASpecialCaseConversionIsSeenIntoAreThoseTheRunTimeConvertsIntoTest.LOWER;
import static souther.compiler.regex.TheStringsASpecialCaseConversionIsSeenIntoAreThoseTheRunTimeConvertsIntoTest.UPPER;
import static souther.compiler.regex.TheStringsASpecialCaseConversionIsSeenIntoAreThoseTheRunTimeConvertsIntoTest.agreesWithTheRunTime;
import static souther.compiler.regex.TheStringsASpecialCaseConversionIsSeenIntoAreThoseTheRunTimeConvertsIntoTest.everyValue;

/**
 * What is seen of a conversion into a language agrees with the run time over every value of up to
 * three code points of the alphabet: the claim of
 * {@link TheStringsASpecialCaseConversionIsSeenIntoAreThoseTheRunTimeConvertsIntoTest}, asked of a
 * third code point as well, which puts one between two others.
 *
 * <p>Deferred to the night for what it costs: the values are the alphabet's size to the third, and
 * each is asked of every language and of both conversions. No smaller set stands for it, since what
 * it adds is every string of three. What it finds is as well found by the morning as by the change
 * that caused it, because what a conversion turns on beside a code point is asked of every change
 * by the class named above, over every value of two.
 */
@Nightly
class EveryValueOfThreeCodePointsIsSeenIntoALanguageAsTheRunTimeConvertsItTest {

    private static final List<String> EVERY_VALUE = everyValue(3);

    @Test
    void lowercaseIsSeenIntoALanguageAsTheRunTimeConvertsIntoIt() {
        agreesWithTheRunTime(LOWER, EVERY_VALUE);
    }

    @Test
    void uppercaseIsSeenIntoALanguageAsTheRunTimeConvertsIntoIt() {
        agreesWithTheRunTime(UPPER, EVERY_VALUE);
    }
}
