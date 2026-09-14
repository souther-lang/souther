package souther.compiler.regex;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every shape the grammar can write is read as the engine reads it, or is not read at all.
 *
 * <p>The patterns are generated rather than listed. A list is what somebody thought of, and what a
 * reading gets wrong is what nobody thought of: {@code ^} was read as adding nothing wherever it
 * stood, and the list had it only at the front of a pattern, where that is true. So the shapes are
 * put together out of the grammar — every leaf in every place a leaf goes, under every way of
 * repeating and joining them — and the ones that would have caught it come out whether anybody
 * expected them or not.
 *
 * <p><b>Two things are checked and they are different promises.</b> A pattern this says it read has
 * to accept the strings {@code java.util.regex} accepts and no others, which is the promise every
 * measure downstream rests on. And a pattern the engine refuses to compile may not be one this says
 * it read: there is no language to agree with, and reading it would be this compiler answering for a
 * pattern its author cannot run.
 *
 * <p>Not read is always allowed. What this reads is a subset, and a pattern outside it leaves the
 * position wider than the rules are — true, and short of what was written. So the generator says
 * nothing about how much has to be read; it says that what is read is right.
 */
class EveryShapeTheGrammarWritesIsReadAsTheEngineReadsItTest {

    /**
     * The smallest pieces a pattern is written out of, one of each kind the grammar has.
     *
     * <p>Anchors among them, which is the point: put where leaves go, they land at the front of a
     * sequence, at the back, between two symbols, inside a group, under a repetition and in an arm
     * of a choice, and each of those is a different question about what they come to.
     *
     * <p>And the pieces that are not pieces. A bare <code>{</code> is a character to some engines
     * and a syntax error to Java, and a bare {@code *} follows nothing — the generator writes them
     * where a leaf goes and the agreement below says what has to happen.
     */
    private static final List<String> LEAVES =
            List.of("a", "b", ".", "[ab]", "[^a]", "\\d", "^", "$", "", "{", "*");

    /** Every way this grammar puts one pattern together out of smaller ones. */
    private static List<String> around(String one, String other) {
        return List.of(one + other, one + "|" + other, "(?:" + one + ")" + other,
                one + "?", one + "*", one + "+", one + "{2}", one + "{1,2}",
                "(?:" + one + "|" + other + ")+", "(?:" + one + ")|(?:" + other + ")");
    }

    /** Strings on either side of what those shapes say, the ones a walk over units gets wrong
     *  included. */
    private static final List<String> STRINGS = strings();

    private static List<String> strings() {
        List<String> out = new ArrayList<>(List.of(
                "", "a", "b", "aa", "ab", "ba", "bb", "aaa", "abc", "c", "1", "12", "a1",
                "{", "{}", "a{", "*", "a*", "[", ".", "aab", "\n", " "));
        out.add(new String(Character.toChars(0x10330)));
        out.add("\ud800");
        return List.copyOf(out);
    }

    /** More than anything here asks for. What is under test is the language and not the
     *  allowance. */
    private static Meter plenty() {
        return new Meter(100_000, 10_000_000);
    }

    /** Every shape of two leaves, and every shape of one of those beside a leaf. */
    private static Set<String> written() {
        Set<String> out = new LinkedHashSet<>(LEAVES);
        for (String one : LEAVES) {
            for (String other : LEAVES) {
                out.addAll(around(one, other));
            }
        }
        Set<String> deeper = new LinkedHashSet<>(out);
        for (String one : out) {
            for (String other : LEAVES) {
                deeper.addAll(around(one, other));
            }
        }
        return deeper;
    }

    /**
     * What this reads, it reads as the engine does; what the engine refuses, this refuses too.
     *
     * <p>Both in one walk, because they are two ways of getting the same pattern wrong and a
     * generator that ran the first alone would report a pattern Java cannot compile as agreeing
     * with it over every string.
     */
    @Test
    void whatIsReadAgreesWithTheEngineAndWhatTheEngineRefusesIsNotRead() {
        List<String> apart = new ArrayList<>();
        int read = 0;
        for (String regex : written()) {
            PatternRead said = PatternParser.read(regex);
            if (!(said instanceof PatternRead.Read it)) {
                continue;
            }
            read++;
            java.util.regex.Pattern engine;
            try {
                engine = java.util.regex.Pattern.compile(regex);
            } catch (java.util.regex.PatternSyntaxException _) {
                apart.add(written(regex) + " is read here and refused by the engine");
                continue;
            }
            Automaton machine = Automaton.of(it.syntax(), plenty());
            if (machine == null) {
                apart.add(written(regex) + " is read and not built");
                continue;
            }
            for (String value : STRINGS) {
                boolean mine = machine.accepts(value);
                boolean theirs = engine.matcher(value).matches();
                if (mine != theirs) {
                    apart.add(written(regex) + " over " + written(value)
                            + ": this says " + mine + ", the engine says " + theirs);
                }
            }
        }

        assertEquals(List.of(), apart);
        assertTrue(read > 500, "the generator has to read a good many of them: " + read);
    }

    /**
     * And a string this hands back is one it holds.
     *
     * <p>A language that names a string and refuses it is not a set — which is what a machine
     * stepping over half a surrogate pair is, whatever spelling put it there.
     */
    @Test
    void whatItHandsBackIsWhatItHolds() {
        for (String regex : written()) {
            if (!(PatternParser.read(regex) instanceof PatternRead.Read it)) {
                continue;
            }
            Automaton machine = Automaton.of(it.syntax(), plenty());
            String one = machine == null ? null : machine.shortest();
            if (one != null) {
                assertTrue(machine.accepts(one),
                        () -> written(regex) + " hands back " + written(one)
                                + ", which it says it does not hold");
            }
        }
    }

    private static String written(String value) {
        StringBuilder out = new StringBuilder("\"");
        value.codePoints().forEach(each -> out.append(each < 0x20 || each > 0x7e
                ? "\\u{%x}".formatted(each) : String.valueOf((char) each)));
        return out.append('"').toString();
    }
}
