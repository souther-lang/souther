package souther.compiler.regex;

import java.util.List;
import net.unit8.notation199x.pattern.Meter;
import net.unit8.notation199x.pattern.PatternMeaning;
import net.unit8.notation199x.pattern.PatternParser;
import net.unit8.notation199x.pattern.PatternRead;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The complement of a language is the one machine for the strings it leaves out.
 *
 * <p>{@link Language#not} takes the complement 199x-notation's machine hands back as it is, without
 * making it canonical, and every other way to a language makes the answer canonical. That is this
 * compiler's decision and rests on the machine's promise that the complement of the one machine is
 * the one machine already, which 199x-notation holds of its machines. What is asked here is that a
 * language reached that way is the language reached any other way: equal, hashed alike, and holding
 * the strings it should — which is what a set adding one and a map looking one up ask of it.
 */
class TheComplementOfTheOneMachineIsTheOneMachineTest {

    private static Meter roomy() {
        return new Meter(100_000, 10_000_000, 1_000_000_000L);
    }

    private static Language language(String regex, Meter meter) {
        PatternMeaning syntax =
                assertInstanceOf(PatternRead.Read.class, PatternParser.read(regex), regex).meaning();
        Language made = PatternPlan.of(syntax).compile(meter);
        assertNotNull(made, regex);
        return made;
    }

    /**
     * The complement of a language is the language the same strings come to by another road.
     *
     * <p>The two are built without a step in common past the words: one turns a language over, the
     * other takes the words out of every string, which makes its answer canonical. Equal means the
     * tables are equal, state for state, which is what a language being the one machine for its
     * strings says.
     */
    @Test
    void aComplementIsTheSameLanguageAsTheOneTheStringsComeToOtherwise() {
        Meter meter = roomy();

        Language turned = Language.ofWords(List.of("a"), meter).not(meter);
        Language met = Language.EVERY_STRING.without(List.of("a"), meter);

        assertNotNull(turned);
        assertNotNull(met);
        assertEquals(met, turned, "one set of strings is one machine, however it was reached");
        assertEquals(met.hashCode(), turned.hashCode(), "which is what a map looking one up asks");
    }

    /** And the strings themselves are the ones the complement should hold. */
    @Test
    void aComplementHoldsTheStringsTheLanguageDoesNot() {
        Meter meter = roomy();

        Language left = language("[ab]+", meter).not(meter);

        assertNotNull(left);
        assertTrue(left.has(""), "no letters at all is not one or more of them");
        assertTrue(left.has("c"), "nor is a letter the pattern leaves out");
        assertTrue(left.has("abc"), "nor is a word holding one");
        assertEquals(false, left.has("ab"), "and a word the language holds is not left over");
    }

    /** Turned over twice, a language is itself — table for table, not merely string for string. */
    @Test
    void aLanguageTurnedOverTwiceIsTheOneItWas() {
        Meter meter = roomy();
        Language held = language("[ab]+", meter);

        Language back = held.not(meter).not(meter);

        assertNotNull(back);
        assertEquals(held, back, "the same machine and not only the same strings");
    }
}
