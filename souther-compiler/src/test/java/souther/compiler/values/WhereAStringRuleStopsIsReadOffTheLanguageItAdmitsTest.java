package souther.compiler.values;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Text;
import souther.compiler.regex.Language;
import souther.compiler.regex.Meter;
import souther.compiler.regex.PatternParser;
import souther.compiler.regex.PatternPlan;
import souther.compiler.regex.PatternRead;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a rule about a string leaves the values it is about, read off the strings it admits.
 *
 * <p>Off the language and not off how the rule was written. {@code String.startsWith("JP", value)}
 * admits the strings from {@code "JP"} up to but not including {@code "JQ"}, and so does a pattern
 * accepting the same strings — so the two leave the position between the same two places, and a
 * reading keyed on which library operation was named would answer for one and not the other.
 *
 * <p>The three answers are about three different things, and the tests below are arranged by which:
 * a run the rule names, a language established to name none, and an allowance that ran out. Nothing
 * here folds the last two together — a rule an author can rewrite and a limit they cannot see are
 * the two a report has to tell apart.
 */
class WhereAStringRuleStopsIsReadOffTheLanguageItAdmitsTest {

    /**
     * A prefix is a run: everything it admits begins with the written text, so it begins at that
     * text and ends where the next string past every one of them begins.
     */
    @Test
    void aPrefixNamesTheRunFromItsTextToTheNextStringPastIt() {
        assertEquals(new TextExtent.One(Text.of("JP"), Text.of("JQ")), extentOf("JP[\\s\\S]*"));
    }

    /**
     * And the same run however the rule reaching it was spelled.
     *
     * <p>The two patterns accept the same strings and are one language, so what they leave the
     * position between is one answer. Read off the spelling, {@code startsWith} would have an edge
     * and the class written out by hand would not.
     */
    @Test
    void thesSameStringsLeaveThePositionBetweenTheSamePlaces() {
        assertEquals(extentOf("JP[\\s\\S]*"), extentOf("J(P)[\\s\\S]*"));
        assertEquals(extentOf("JP[\\s\\S]*"), extentOf("JP[\\s\\S]{0,}"));
    }

    /** A rule naming one string is the run holding that string and nothing else. */
    @Test
    void oneStringIsTheRunFromItToTheNextThingAbove() {
        TextExtent one = extentOf("JP");
        TextExtent.One run = assertInstanceOf(TextExtent.One.class, one);
        assertEquals(Text.of("JP"), run.first());
        assertNotNull(run.after());
        assertTrue(run.after().at().startsWith("JP"),
                "what comes after every string beginning with JP and equal to it is JP and a"
                        + " smallest unit: " + run.after());
    }

    /**
     * A rule admitting everything from a string upwards has a beginning and no end.
     *
     * <p>There is no string above every one it admits, so there is nowhere an upper edge could be
     * written — which is a run of the order all the same, and not a run this could not work out.
     *
     * <p>The language is built out of what comes before a string because no pattern says it: every
     * string above {@code "J"} includes the ones written with a pair, and a class over the symbols
     * cannot name those and the basic plane in one range. What is under test here is the reading of
     * the run and not the machine it is handed.
     */
    @Test
    void aRuleAdmittingEverythingAboveAStringHasNoEnd() {
        Meter meter = PatternPlan.Budget.OF_AN_ORDERED_EXTENT.meter();
        Language from = Language.before("J", meter).not(meter);
        assertNotNull(from);
        assertTrue(from.has("J"));
        assertTrue(from.has("𐀀"), "a string written with a pair is above J");
        assertEquals(new TextExtent.One(Text.of("J"), null), TextExtents.of(from));
    }

    /** And everything there is, which begins at the string of nothing and has no end either. */
    @Test
    void everyStringThereIsBeginsAtTheStringOfNothing() {
        assertEquals(new TextExtent.One(Text.of(""), null), extentOf("[\\s\\S]*"));
    }

    /**
     * Two prefixes are two runs, and what that comes to is that no one run is named.
     *
     * <p>The answer is not that the strings are not convex. What follows is that there is no single
     * pair of places to put an edge at, which is what this says — and a reading that answered with
     * the reason would be saying something about the shape of the language rather than about where
     * the values stop.
     */
    @Test
    void twoPrefixesNameNoOneRun() {
        assertEquals(new TextExtent.NoNamedRun(), extentOf("(JP|US)[\\s\\S]*"));
    }

    /**
     * And a language whose strings descend without stopping names none either, for the other of the
     * two reasons.
     *
     * <p>{@code a*b} holds a string below every string it holds. There is no least, so there is no
     * place a lower edge could be written — and answering with the shortest would put a line where
     * the values do not stop.
     */
    @Test
    void aLanguageDescendingWithoutStoppingNamesNoRun() {
        assertEquals(new TextExtent.NoNamedRun(), extentOf("a*b"));
    }

    /**
     * A run whose ends are a pair and a lone surrogate is read on the runtime's order.
     *
     * <p>The prefix is the one pair, so what it admits runs from that pair up to the pair after it.
     * On the order the symbols of a machine are in, the string after would be somewhere else
     * entirely — every pair is above every unit there, and the two disagree about which of two
     * strings beginning with the same unit comes first.
     */
    @Test
    void aRunAcrossThePairsIsReadOnTheRuntimesOrder() {
        assertEquals(new TextExtent.One(Text.of("𐀀"), Text.of("𐀁")),
                extentOf("𐀀[\\s\\S]*"));
    }

    /**
     * And a lone surrogate beside a pair is read as the string it is.
     *
     * <p>A high surrogate and a low one standing next to each other are the pair, which is what a
     * matcher reads and what a walk over a string takes in. Read as two symbols, the run of the pair
     * would end at the pair itself — the walk would answer with a sequence of symbols no string is
     * written as, and the language would be said to hold a string it does not.
     */
    @Test
    void aHighSurrogateBesideALowOneIsThePairAndNotTwoSymbols() {
        Language pair = languageOf("𐀀[\\s\\S]*");
        String least = pair.least();
        assertEquals("𐀀", least);
        assertTrue(pair.has(least), "the least string it holds is one it holds");
    }

    /**
     * An allowance that runs out is said as itself, and never as a language that names no run.
     *
     * <p>The two read alike and are opposite claims: one is about the strings a rule admits and the
     * other about what this compiler was allowed to build. A reader shown the first would tell an
     * author their rule draws no line, of a rule that draws one.
     */
    @Test
    void anAllowanceThatRanOutIsSaidAsItself() {
        Language prefix = languageOf("JP[\\s\\S]*");
        assertInstanceOf(TextExtent.NotBuilt.class,
                TextExtents.of(prefix, new Meter(2, 2)),
                "a rule that names a run under an allowance that holds nothing");
    }

    /** And which limit refused it, since the two are not one fact. */
    @Test
    void andWhichLimitRefusedIt() {
        Language prefix = languageOf("JP[\\s\\S]*");
        TextExtent.NotBuilt one = assertInstanceOf(TextExtent.NotBuilt.class,
                TextExtents.of(prefix, new Meter(2, 1000)));
        assertEquals(Meter.Stopped.ONE_MACHINE, one.stopped());

        TextExtent.NotBuilt all = assertInstanceOf(TextExtent.NotBuilt.class,
                TextExtents.of(prefix, new Meter(100_000, 3)));
        assertEquals(Meter.Stopped.THE_ANSWER, all.stopped());
    }

    /** A run has a string at its lower end and none just below its upper: the shape is the one
     *  thing the type will hold. */
    @Test
    void aRunHasNoOtherShape() {
        assertNull(new TextExtent.One(Text.of("JP"), null).after());
        assertThrows(() -> new TextExtent.One(null, Text.of("JQ")));
        assertThrows(() -> new TextExtent.One(Text.of("JQ"), Text.of("JP")));
        assertThrows(() -> new TextExtent.One(Text.of("JP"), Text.of("JP")));
    }

    private static void assertThrows(Runnable what) {
        org.junit.jupiter.api.Assertions.assertThrows(IllegalArgumentException.class,
                what::run);
    }

    /** What the rule written as {@code pattern} leaves the position between. */
    private static TextExtent extentOf(String pattern) {
        return TextExtents.of(languageOf(pattern));
    }

    /** The strings {@code pattern} accepts. */
    private static Language languageOf(String pattern) {
        PatternRead read = PatternParser.read(pattern);
        assertInstanceOf(PatternRead.Read.class, read, pattern + " is read");
        Language made = PatternPlan.of(((PatternRead.Read) read).syntax())
                .compile(PatternPlan.Budget.OF_ADMITTED_VALUES.meter());
        assertNotNull(made, pattern + " compiles");
        return made;
    }
}
