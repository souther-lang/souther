package souther.compiler.codegen;

import org.junit.jupiter.api.Test;

import souther.compiler.regex.Language;
import souther.compiler.regex.Meter;
import souther.compiler.regex.PatternMeaning;
import souther.compiler.regex.PatternParser;
import souther.compiler.regex.PatternPlan;
import souther.compiler.regex.PatternRead;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;
import java.util.regex.Pattern;
import java.util.regex.PatternSyntaxException;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the JVM runs for a pattern accepts the strings the pattern means, and no others.
 *
 * <p>The JVM's matcher is handed what {@link JavaPatterns} writes from the meaning the checker read,
 * never the author's text, so this is the whole of what makes a run-time {@code String.matches}
 * answer what the language says. Held against the machine the meaning builds — the one the analysis
 * and the compiler's folds read — rather than against the engine reading the author's text, which
 * would be asking the engine to agree with itself.
 *
 * <p>The patterns are generated out of the grammar rather than listed, so every shape the writer has
 * an arm for is reached in every place it can stand: a choice inside a sequence, a repetition of a
 * repetition, a group of nothing repeated, a set of no symbol, a symbol the engine reads specially.
 */
class WhatTheJvmRunsIsWhatThePatternMeansTest {

    /** The pieces, each a kind of thing the writer spells differently. */
    private static final List<String> LEAVES = List.of(
            "a", "1", ".", "[ab]", "[^a]", "\\d", "\\s", "\\W", "^", "$", "",
            "\\-", "\\.", "\\\\", "[\\]\\^\\-]", " ", "\\x{10330}", "[^\\x{0}-\\x{10FFFF}]",
            "\\n", "\\x{85}");

    private static List<String> around(String one, String other) {
        return List.of(one + other, one + "|" + other, "(?:" + one + ")" + other,
                one + "?", one + "*", one + "+", one + "{2}", one + "{1,2}", one + "{0,}",
                "(?:" + one + "|" + other + ")+", "(?:" + one + "*)*", "(?:" + one + ")|(?:" + other
                        + ")");
    }

    private static final List<String> STRINGS = strings();

    private static List<String> strings() {
        List<String> out = new ArrayList<>(List.of(
                "", "a", "1", "aa", "a1", "1a", "11", "ab", "b", "bb", "ba", " ", "  ", "a ",
                "-", ".", "\\", "]", "^", "-.", "\n", "\r", "a\n", "\n\n", "\t", "é",
                String.valueOf((char) 0x85), String.valueOf((char) 0x2028)));
        out.add(new String(Character.toChars(0x10330)));
        out.add(new String(Character.toChars(0x10330)) + "a");
        out.add(new String(Character.toChars(0x10FFFF)));
        return List.copyOf(out);
    }

    private static Set<String> written() {
        Set<String> out = new LinkedHashSet<>(LEAVES);
        for (String one : LEAVES) {
            for (String other : LEAVES) {
                out.addAll(around(one, other));
            }
        }
        Set<String> deeper = new LinkedHashSet<>(out);
        for (String one : out) {
            for (String other : List.of("a", "^", "")) {
                deeper.addAll(around(one, other));
            }
        }
        return deeper;
    }

    private static Meter plenty() {
        return new Meter(100_000, 10_000_000);
    }

    @Test
    void theEngineAcceptsWhatTheMeaningAccepts() {
        List<String> apart = new ArrayList<>();
        int asked = 0;
        for (String regex : written()) {
            if (!(PatternParser.read(regex) instanceof PatternRead.Read read)) {
                continue;
            }
            Language meant = PatternPlan.of(read.meaning()).compile(plenty());
            String lowered = JavaPatterns.of(read.meaning());
            Pattern engine;
            try {
                engine = Pattern.compile(lowered);
            } catch (PatternSyntaxException e) {
                apart.add(regex + " is written as " + lowered + ", which the engine refuses: "
                        + e.getDescription());
                continue;
            }
            asked++;
            for (String value : STRINGS) {
                boolean mine = meant.has(value);
                boolean theirs = engine.matcher(value).matches();
                if (mine != theirs) {
                    apart.add(regex + " written as " + lowered + " over " + shown(value)
                            + ": the meaning says " + mine + ", the engine says " + theirs);
                }
            }
        }

        assertEquals(List.of(), apart);
        assertTrue(asked > 1000, "the generator reached the writer: " + asked);
    }

    /**
     * And what is written says nothing whose meaning is the engine's to decide.
     *
     * <p>No {@code .}, no shorthand class, no anchor, no {@code ^} but the one that negates a class:
     * each of those means what the engine and its flags say, and the agreement above holds only for
     * the flags this suite runs under. A number, a group that captures nothing and a count mean the
     * same under every reading of the engine's.
     */
    @Test
    void whatIsWrittenLeavesNothingToTheEngine() {
        List<String> engines = new ArrayList<>();
        for (String regex : written()) {
            if (PatternParser.read(regex) instanceof PatternRead.Read read) {
                String lowered = JavaPatterns.of(read.meaning());
                if (!onlyNumbersCountsAndGroups(lowered)) {
                    engines.add(regex + " is written as " + lowered);
                }
            }
        }

        assertEquals(List.of(), engines);
    }

    /** A pattern as short as it can be written reads as the author would write it. */
    @Test
    void aFormatReadsAsItWasWritten() {
        assertEquals("[0-9]{3}\\-[0-9]{4}", lowered("[0-9]{3}-[0-9]{4}"));
        assertEquals("T[0-9]{13}", lowered("^T\\d{13}$"));
        assertEquals("(?:ab|c)d", lowered("(ab|c)d"));
    }

    private static String lowered(String regex) {
        PatternMeaning meaning = ((PatternRead.Read) PatternParser.read(regex)).meaning();
        return JavaPatterns.of(meaning);
    }

    private static boolean onlyNumbersCountsAndGroups(String lowered) {
        for (int at = 0; at < lowered.length(); at++) {
            char c = lowered.charAt(at);
            if (c == '\\') {
                char next = lowered.charAt(at + 1);
                if (Character.isLetter(next) && next != 'x') {
                    return false;
                }
                at++;
            } else if (c == '.' || c == '$' || (c == '^' && (at == 0 || lowered.charAt(at - 1) != '['))) {
                return false;
            }
        }
        return true;
    }

    private static String shown(String value) {
        StringBuilder out = new StringBuilder("\"");
        value.codePoints().forEach(each -> out.append(each >= 0x20 && each < 0x7f
                ? String.valueOf((char) each) : String.format("\\x{%X}", each)));
        return out.append('"').toString();
    }
}
