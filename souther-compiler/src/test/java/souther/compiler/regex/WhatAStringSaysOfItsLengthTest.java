package souther.compiler.regex;

import net.unit8.notation199x.pattern.CodePoints;
import net.unit8.notation199x.pattern.PatternMeaning;
import org.junit.jupiter.api.Test;

import souther.compiler.regex.WhatAStringSaysOfItsLength.Condition;
import souther.compiler.regex.WhatAStringSaysOfItsLength.Sides;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a string standing in a language, or inside another, says of how long it is, on each side of
 * the statement — the conditions of a side, and never the denial of the other's.
 */
class WhatAStringSaysOfItsLengthTest {

    private static final PatternMeaning DIGIT = new PatternMeaning.Symbols(CodePoints.DIGITS);

    private static Sides<String> in(PatternMeaning meaning) {
        return WhatAStringSaysOfItsLength.inALanguage("s", meaning);
    }

    @Test
    void aPatternOfOneLengthIsThatLengthWhereItIsAcceptedAndSaysNothingWhereItIsNot() {
        PatternMeaning three = new PatternMeaning.Repeated(DIGIT, 3, 3);
        assertEquals(new Sides<>(
                List.of(new Condition.AtLeast<>("s", 3), new Condition.AtMost<>("s", 3)),
                List.of()), in(three));
    }

    @Test
    void aPatternThatAcceptsTheEmptyStringLeavesAStringItDoesNotAcceptNotEmpty() {
        PatternMeaning any = new PatternMeaning.Repeated(DIGIT, 0, PatternMeaning.Repeated.NO_CEILING);
        assertEquals(new Sides<>(List.of(), List.of(new Condition.AtLeast<>("s", 1))), in(any));
    }

    @Test
    void aPatternWithNoCeilingIsOnlyBoundedBelowWhereItIsAccepted() {
        PatternMeaning some = new PatternMeaning.Repeated(DIGIT, 1, PatternMeaning.Repeated.NO_CEILING);
        assertEquals(new Sides<>(List.of(new Condition.AtLeast<>("s", 1)), List.of()), in(some));
    }

    @Test
    void aPatternNothingSatisfiesIsAcceptedByNoStringAndSaysNothingOfOneItDoesNotAccept() {
        assertEquals(new Sides<>(List.of(new Condition.Impossible<>()), List.of()),
                in(new PatternMeaning.Never()));
    }

    @Test
    void aStringInsideAnotherIsNoLongerAndOneNotInsideItIsNotEmpty() {
        assertEquals(new Sides<>(List.of(new Condition.NoLongerThan<>("a", "b")),
                List.of(new Condition.AtLeast<>("a", 1))),
                WhatAStringSaysOfItsLength.inside("a", "b"));
    }

    @Test
    void aStringWhoseLengthIsNotNamedLeavesWhatNeedsItUnsaid() {
        assertEquals(new Sides<>(List.of(), List.of(new Condition.AtLeast<>("a", 1))),
                WhatAStringSaysOfItsLength.inside("a", null));
        assertEquals(new Sides<>(List.of(), List.of()),
                WhatAStringSaysOfItsLength.inside(null, "b"));
    }
}
