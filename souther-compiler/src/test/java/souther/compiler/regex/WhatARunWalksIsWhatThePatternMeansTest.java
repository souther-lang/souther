package souther.compiler.regex;

import org.junit.jupiter.api.Test;
import souther.runtime.StringPattern;

import java.time.Duration;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a class runs for a pattern accepts the strings the pattern means, and no others.
 *
 * <p>A class runs one of two machines ({@link PatternImage}): the deterministic one, or the one the
 * pattern's shape builds where making it deterministic costs too much. Both are held here against
 * the recognizer the compiler folds a match with, and against each other. Which one a class holds is
 * picked by size, so a small pattern would only ever reach the deterministic one; each is built here
 * directly, so the other is asked too.
 *
 * <p>The patterns are generated out of the grammar rather than listed, so every shape a machine is
 * built from is reached in every place it can stand: a choice inside a sequence, a repetition of a
 * repetition, a group of nothing repeated, a set of no symbol.
 */
class WhatARunWalksIsWhatThePatternMeansTest {

    /** The pieces, each a kind of thing a machine is built from differently. */
    private static final List<String> LEAVES = List.of(
            "a", "1", ".", "[ab]", "[^a]", "\\d", "\\s", "\\W", "^", "$", "",
            "\\-", "\\.", "\\\\", "[\\]\\^\\-]", " ", "\\x{10330}", "[^\\x{0}-\\x{10FFFF}]",
            "\\n", "\\x{85}", "\0");

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
                "-", ".", "\\", "]", "^", "-.", "\n", "\r", "a\n", "\n\n", "\t", "é", "\0", "\0a",
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
        return new Meter(100_000, 10_000_000, 1_000_000_000L);
    }

    /**
     * Every piece is a pattern.
     *
     * <p>The walk below asks only what the reader reads, and passes over what it refuses. A piece
     * the reader wrongly refused would leave every pattern built from it out of the walk, and the
     * walk would stay green having asked nothing about it.
     */
    @Test
    void everyPieceIsRead() {
        for (String leaf : LEAVES) {
            assertInstanceOf(PatternRead.Read.class, PatternParser.read(leaf), shown(leaf));
        }
    }

    @Test
    void bothMachinesAcceptWhatTheMeaningAccepts() {
        List<String> apart = new ArrayList<>();
        int asked = 0;
        for (String regex : written()) {
            if (!(PatternParser.read(regex) instanceof PatternRead.Read read)) {
                continue;
            }
            Recognizer meant = Recognizer.of(read.meaning(), plenty());
            StringPattern deterministic =
                    StringPattern.of(PatternImage.deterministic(read.meaning(), plenty()));
            StringPattern shaped = StringPattern.of(PatternImage.shaped(read.meaning(), plenty()));
            asked++;
            for (String value : STRINGS) {
                boolean mine = meant.accepts(value, plenty()).orElseThrow();
                if (deterministic.matches(value) != mine) {
                    apart.add(regex + " over " + shown(value) + ": the meaning says " + mine
                            + ", the deterministic machine does not");
                }
                if (shaped.matches(value) != mine) {
                    apart.add(regex + " over " + shown(value) + ": the meaning says " + mine
                            + ", the shape's machine does not");
                }
            }
        }

        assertEquals(List.of(), apart);
        assertTrue(asked > 1000, "the generator reached the machines: " + asked);
    }

    /**
     * Half a surrogate pair is no {@code String}, and a set that holds every symbol does not hold
     * it: a walk refuses it where the fold does.
     */
    @Test
    void halfASurrogatePairIsAcceptedByNothing() {
        String half = String.valueOf((char) 0xD800);
        PatternMeaning any = ((PatternRead.Read) PatternParser.read("[\\x{0}-\\x{10FFFF}]*"))
                .meaning();
        assertFalse(Recognizer.of(any, plenty()).accepts(half, plenty()).orElseThrow());
        assertFalse(StringPattern.of(PatternImage.deterministic(any, plenty())).matches(half));
        assertFalse(StringPattern.of(PatternImage.shaped(any, plenty())).matches(half));
    }

    /**
     * A pattern whose deterministic machine is past what a class makes deterministic runs as the
     * machine its shape builds, and answers the same.
     *
     * <p>{@code .*a.{20}} is a few dozen states as its shape, and deterministic it has to remember
     * where each of the last twenty-one characters was an {@code a}.
     */
    @Test
    void aPatternTooLargeToMakeDeterministicIsRunAsItsShape() {
        PatternMeaning meaning = ((PatternRead.Read) PatternParser.read(".*a.{20}")).meaning();
        assertEquals(null, PatternImage.deterministic(meaning,
                PatternPlan.Budget.OF_A_DETERMINISTIC_RUN.meter()));
        PatternImage.Written image = assertInstanceOf(PatternImage.Written.class,
                PatternImage.of(meaning));
        assertEquals(image.strings(), PatternImage.shaped(meaning, PatternPlan.Budget.OF_A_RUN.meter()));

        StringPattern run = StringPattern.of(image.strings());
        assertTrue(run.matches("xa" + "b".repeat(20)));
        assertFalse(run.matches("xa" + "b".repeat(19)));
        assertFalse(run.matches("x".repeat(40)));
    }

    /**
     * A deterministic machine whose ASCII characters are all told apart, and whose states are many,
     * is past the table a walk looks ASCII up in, and walks by its runs with the same answers.
     *
     * <p>Every ASCII character written in turn, five times over: each character is a kind of its
     * own and there is a state for each place in the text.
     */
    @Test
    void aMachineTooWideForItsAsciiTableAnswersByItsRuns() {
        StringBuilder regex = new StringBuilder();
        StringBuilder text = new StringBuilder();
        for (int copy = 0; copy < 5; copy++) {
            for (int c = 0; c < 128; c++) {
                regex.append(String.format("\\x{%X}", c));
                text.append((char) c);
            }
        }
        PatternMeaning meaning = ((PatternRead.Read) PatternParser.read(regex.toString())).meaning();
        StringPattern run = StringPattern.of(PatternImage.deterministic(meaning, plenty()));
        String whole = text.toString();

        assertTrue(run.matches(whole));
        assertFalse(run.matches(whole.substring(0, whole.length() - 1)));
        assertFalse(run.matches(whole.substring(0, 300) + "é" + whole.substring(301)));
        assertFalse(run.matches(whole.substring(0, 300) + "a" + whole.substring(301)));
    }

    /** Past what a class runs as its shape, there is no machine and nothing else runs it. */
    @Test
    void aPatternWhoseShapeIsLargerThanAClassRunsHasNoImage() {
        PatternMeaning meaning = ((PatternRead.Read) PatternParser.read("(a{1000}){1000}")).meaning();
        assertEquals(new PatternImage.MoreStates(PatternPlan.Budget.OF_A_RUN.mostStates()),
                PatternImage.of(meaning));
    }

    /**
     * What a backtracking matcher spends a lifetime on, a walk answers at once.
     *
     * <p>A counted repetition nested in another, over a run the last character refuses, is
     * exponential in the length for a matcher that tries each way of dividing the run; an
     * alternation under a star recursed once per character in one and ran out of stack. A walk
     * reads each character once, so these lengths are nothing to it.
     */
    @Test
    void theShapesThatDefeatABacktrackingMatcherAreOneWalk() {
        assertTimeoutPreemptively(Duration.ofSeconds(30), () -> {
            for (PatternImage.Written image : List.of(
                    written("(a{0,30}){0,30}b"), written("(?:a|b)*"), written("(.*a){12}c"))) {
                StringPattern run = StringPattern.of(image.strings());
                run.matches("a".repeat(200_000));
            }
            assertFalse(StringPattern.of(written("(a{0,30}){0,30}b").strings())
                    .matches("a".repeat(200_000)));
            assertTrue(StringPattern.of(written("(?:a|b)*").strings())
                    .matches("ab".repeat(100_000)));
        });
    }

    private static PatternImage.Written written(String regex) {
        PatternMeaning meaning = ((PatternRead.Read) PatternParser.read(regex)).meaning();
        return assertInstanceOf(PatternImage.Written.class, PatternImage.of(meaning));
    }

    private static String shown(String value) {
        StringBuilder out = new StringBuilder("\"");
        value.codePoints().forEach(each -> out.append(each >= 0x20 && each < 0x7f
                ? String.valueOf((char) each) : String.format("\\x{%X}", each)));
        return out.append('"').toString();
    }
}
