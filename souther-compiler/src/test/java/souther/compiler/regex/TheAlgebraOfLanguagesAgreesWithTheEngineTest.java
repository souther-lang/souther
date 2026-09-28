package souther.compiler.regex;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the operations say a language holds is what the strings themselves say.
 *
 * <p>Each of them is a claim about membership: a meet holds what both hold, a join holds what either
 * does, a complement holds what one does not. So each is asked that way — over every pair of
 * patterns and every string of a sample, against the engine that decides the two sides.
 *
 * <p>Emptiness and everything-ness are the two that cannot be asked of a sample, since no list of
 * strings shows that none is left or that none is missing. They are asked of languages built to be
 * one or the other, and held to the answer the sample cannot give.
 */
class TheAlgebraOfLanguagesAgreesWithTheEngineTest {

    /** More than anything here asks for, so that what is measured is the algebra and never the
     *  allowance. A fresh one each time, since a meter is spent as it is used. */
    private static Meter plenty() {
        return new Meter(100_000, 10_000_000);
    }

    private static final List<String> PATTERNS = List.of(
            "a+", "a*", "[ab]+", "b", "0|1", "a|b", "b|c", "[0-9]{2}",
            "[0-9]+", "[a-z]+", ".", "[^a]", "x?", "(?:ab)+", "\\d\\d?");

    private static final List<String> STRINGS = List.of(
            "", "a", "b", "c", "x", "0", "1", "ab", "ba", "aa", "bb", "00", "01", "12",
            "abab", "aab", "z", " ", "\n", "9", "99", "999");

    private static Automaton machine(String regex) {
        PatternMeaning syntax = assertInstanceOf(PatternRead.Read.class,
                PatternParser.read(regex), regex).meaning();
        Automaton made = Automaton.of(syntax, plenty());
        assertNotNull(made, regex);
        return made;
    }

    /** The three operations, each under an allowance nothing here reaches. What is under test is
     *  what they come to, so a refusal would be this test running out rather than an answer. */
    private static Automaton and(Automaton one, Automaton other) {
        return made(one.and(other, plenty()));
    }

    private static Automaton or(Automaton one, Automaton other) {
        return made(one.or(other, plenty()));
    }

    private static Automaton not(Automaton one) {
        return made(one.not(plenty()));
    }

    private static Automaton made(Automaton machine) {
        assertNotNull(machine, "the machines here are within what this test allows");
        return machine;
    }

    private static boolean engineTakes(String regex, String value) {
        return java.util.regex.Pattern.compile(regex).matcher(value).matches();
    }

    /** A meet holds what both hold. */
    @Test
    void bothOfThemHoldsWhatEachDoes() {
        List<String> apart = new ArrayList<>();
        for (String one : PATTERNS) {
            for (String two : PATTERNS) {
                Automaton met = and(machine(one), machine(two));
                for (String value : STRINGS) {
                    boolean said = met.accepts(value);
                    boolean both = engineTakes(one, value) && engineTakes(two, value);
                    if (said != both) {
                        apart.add(one + " and " + two + " over \"" + value + "\"");
                    }
                }
            }
        }
        assertEquals(List.of(), apart);
    }

    /** A join holds what either holds. */
    @Test
    void eitherOfThemHoldsWhatOneOfThemDoes() {
        List<String> apart = new ArrayList<>();
        for (String one : PATTERNS) {
            for (String two : PATTERNS) {
                Automaton joined = or(machine(one), machine(two));
                for (String value : STRINGS) {
                    boolean said = joined.accepts(value);
                    boolean either = engineTakes(one, value) || engineTakes(two, value);
                    if (said != either) {
                        apart.add(one + " or " + two + " over \"" + value + "\"");
                    }
                }
            }
        }
        assertEquals(List.of(), apart);
    }

    /** And a complement holds what its language does not, over every symbol there is. */
    @Test
    void whatIsLeftOutHoldsWhatIsNotIn() {
        List<String> apart = new ArrayList<>();
        for (String one : PATTERNS) {
            Automaton left = not(machine(one));
            for (String value : STRINGS) {
                boolean said = left.accepts(value);
                if (said == engineTakes(one, value)) {
                    apart.add("not " + one + " over \"" + value + "\"");
                }
            }
        }
        assertEquals(List.of(), apart);
    }

    /**
     * Whether it holds nothing, and whether it holds everything, asked the way anything asks them.
     *
     * <p>Of the canonical machine, because that is the only kind a {@link Language} is and so the
     * only kind either question is ever put to. Asked of a machine as it came out of an operation,
     * these would be a second way of answering them — and the day the two disagreed, the one under
     * test here is not the one a reading believes.
     */
    private static boolean holdsNothing(Automaton machine) {
        return settled(machine).holdsNothing();
    }

    private static boolean holdsEverything(Automaton machine) {
        return settled(machine).holdsEverything();
    }

    private static Automaton settled(Automaton machine) {
        Automaton one = machine.canonical(plenty());
        assertNotNull(one, "the machines here are small enough to make canonical");
        return one;
    }

    /** A language and its complement hold nothing between them, and everything together. */
    @Test
    void aLanguageAndWhatItLeavesOutAreTwoHalves() {
        for (String each : PATTERNS) {
            Automaton one = machine(each);
            assertTrue(holdsNothing(and(one, not(one))), each + " and what it leaves out");
            assertTrue(holdsEverything(or(one, not(one))), each + " or what it leaves out");
        }
    }

    /** Emptiness is about what is left, which no list of strings shows. */
    @Test
    void whatHoldsNothingSaysSo() {
        assertTrue(holdsNothing(and(machine("a"), machine("b"))), "no string is both");
        assertFalse(holdsNothing(and(machine("a|b"), machine("b|c"))), "`b` is both");
        assertFalse(holdsNothing(machine("a")));
        assertTrue(holdsNothing(and(machine("[0-9]"), machine("[a-z]"))));
    }

    /** And everything-ness is about what is missing, which no list of strings shows either. */
    @Test
    void whatHoldsEverythingSaysSo() {
        assertTrue(holdsEverything(machine("[\\x{0}-\\x{10FFFF}]*")));
        assertFalse(holdsEverything(machine(".*")),
                "a dot leaves out the line terminators, so the strings holding one are missing");
        assertFalse(holdsEverything(machine("a*")));
        assertFalse(holdsEverything(machine("[^a]*")));
        assertTrue(holdsEverything(or(machine("a*"), not(machine("a*")))));
    }

    /**
     * One string of the language, wherever there is one.
     *
     * <p>Held to emptiness rather than to a list: whatever is not empty answers, and whatever is
     * empty answers with nothing. The two coming apart is what would let a reading report a language
     * as unwritable when it is only this compiler that could not find a value.
     */
    @Test
    void whateverHoldsSomethingHandsOneBack() {
        for (String one : PATTERNS) {
            for (String two : PATTERNS) {
                Automaton met = and(machine(one), machine(two));
                String said = met.shortest();
                if (holdsNothing(met)) {
                    assertNull(said, one + " and " + two);
                } else {
                    assertNotNull(said, one + " and " + two + " holds something");
                    assertTrue(met.accepts(said), said + " is one of them");
                    assertTrue(engineTakes(one, said) && engineTakes(two, said),
                            "\"" + said + "\" is taken by both " + one + " and " + two);
                }
            }
        }
    }

    /** The shortest of them, and the same one on two runs. */
    @Test
    void theOneItHandsBackIsTheShortestAndAlwaysTheSame() {
        assertEquals("00", machine("[0-9]{2}").shortest());
        assertEquals("", machine("a*").shortest());
        assertEquals("a", machine("a+").shortest());
        assertEquals("b", machine("(a|aa)*b").shortest());
        assertEquals("0", machine("0|1").shortest());

        for (String each : PATTERNS) {
            assertEquals(machine(each).shortest(), machine(each).shortest(), each);
        }
    }

    /**
     * A value that can be written is preferred, and never at the price of a longer one.
     *
     * <p>Both halves. A language whose shortest strings are all unwritable answers with one of them
     * rather than reaching for a longer one that can be pasted — what was asked for is a string of
     * the language, and the length is settled before anything is preferred.
     */
    @Test
    void whatCanBeWrittenIsPreferredAmongTheShortest() {
        assertEquals("\t", machine("[\\x{0}-\\x{7F}]").shortest(),
                "the symbols under it are ones no source carries, and the tab is the least of the"
                        + " ones one does");
        assertEquals(String.valueOf((char) 0), machine("[\\x{0}-\\x{8}]").shortest(),
                "nothing of that length can be written, so one that cannot is the answer");
        assertEquals(1, machine("[\\x{0}-\\x{8}]|ab").shortest().length(),
                "and never a longer string for being writable");
    }
}
