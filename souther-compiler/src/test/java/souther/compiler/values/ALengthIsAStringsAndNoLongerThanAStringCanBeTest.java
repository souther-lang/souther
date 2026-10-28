package souther.compiler.values;

import org.junit.jupiter.api.Test;

import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;
import souther.compiler.regex.PatternPlan;

import java.math.BigDecimal;
import java.util.LinkedHashSet;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Values held to a length are strings, each no longer than a {@code String} can be. Asked whether
 * such values hold one, the answer is about those strings, whatever the set beside the length
 * names past them.
 */
class ALengthIsAStringsAndNoLongerThanAStringCanBeTest {

    /** Every string but one, longer than the longest string: no string is. */
    @Test
    void nothingIsLongerThanTheLongestString() {
        ValuesWithin past = ValuesWithin.longerThan(ValueSet.allBut(new Value.Text("x")),
                TextExtents.LONGEST_STRING);

        assertTrue(past.shownToHoldNone(), "no string is longer than the longest");
        assertFalse(past.shownToHoldAValue());
    }

    /** One length short of it, the strings of the longest length are left. */
    @Test
    void theLongestLengthItselfHoldsStrings() {
        assertTrue(ValuesWithin.longerThan(ValueSet.allBut(new Value.Text("x")),
                TextExtents.LONGEST_STRING - 1).shownToHoldAValue());
    }

    /** A language holding strings of every length holds none past the longest. */
    @Test
    void aLanguageHoldsNoStringPastTheLongest() {
        assertTrue(ValuesWithin.longerThan(matching("[a-z]+"), TextExtents.LONGEST_STRING)
                .shownToHoldNone());
        assertFalse(ValuesWithin.longerThan(matching("[a-z]+"), 3).shownToHoldNone(),
                "and strings longer than three, which it holds");
    }

    /** A number has no length, so values held to one hold no number. */
    @Test
    void aValueThatIsNoStringIsOfNoLength() {
        ValueSet both = ValueSet.oneOf(new LinkedHashSet<>(List.of(
                new Value.Number(BigDecimal.ONE), new Value.Text("ab"))));
        ValuesWithin upToThree = new ValuesWithin(both, 0, 3L);

        assertFalse(upToThree.has(new Value.Number(BigDecimal.ONE)));
        assertTrue(upToThree.has(new Value.Text("ab")));
        assertTrue(new ValuesWithin(ValueSet.oneOf(new LinkedHashSet<>(List.of(
                new Value.Number(BigDecimal.ONE)))), 0, 3L).shownToHoldNone(),
                "and a set of numbers held to a length holds nothing");
        assertTrue(ValuesWithin.all(both).has(new Value.Number(BigDecimal.ONE)),
                "where no length bounds them, the number is one of them");
    }

    private static ValueSet matching(String regex) {
        PatternRead said = PatternParser.read(regex);
        return ValueSet.matching(PatternPlan.of(
                        assertInstanceOf(PatternRead.Read.class, said, regex).meaning())
                .compile(PatternPlan.Budget.OF_ADMITTED_VALUES.meter()));
    }
}
