package souther.compiler.regex;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A pattern this reads accepts the strings the engine accepts, and no others.
 *
 * <p>What the subset promises is not that it is small but that it is exact. A reading that accepted
 * fewer strings than the rule would leave values a row may carry outside the set, and one that
 * accepted more would put values in it the model refuses — and neither shows up as a failure
 * anywhere, since both are still a set and every measure downstream would go on counting.
 *
 * <p>So the answer is held against {@code java.util.regex} itself, over strings chosen to sit either
 * side of the constructs the subset reads. Not a list of pairs somebody thought of: every pattern is
 * asked about every string, so a string that ought to be refused by one pattern and accepted by
 * another is asked of both.
 */
class WhatThisAcceptsIsWhatTheEngineAcceptsTest {

    /** What the example models write, and what the constructs of the subset look like. */
    private static final List<String> PATTERNS = List.of(
            "T[0-9]{13}",
            "[0-9]{2}-[0-9]{6}",
            "0[1-9]|[1-3][0-9]|4[0-7]",
            "[ｦ-ﾟァ-ヴー 　]+",
            "[^@\\s]+@[^@\\s]+\\.[^@\\s]+",
            "\\+?[0-9][0-9 \\-()]{6,19}",
            "006[0-9A-Za-z]{12}([0-9A-Z]{3})?",
            "[a-z0-9]+(?:-[a-z0-9]+)*",
            ".",
            "..",
            ".*",
            ".+",
            "[^a]",
            "[^a]{2}",
            "a{2,6}",
            "a{0,2}",
            "(a|aa)*b",
            "(?:x?x){4}",
            "\\d\\w\\s",
            "\\D",
            "\\S+",
            "[a-]",
            "[]]",
            "x|",
            "|x",
            "(?:)",
            "a?b?c?",
            "\\x{10330}",
            "[\\x{10000}-\\x{10400}]",
            "[^\\x{10330}]",
            "\\u00e9",
            "[\\d-]{2}");

    /** Strings that sit either side of what those patterns say. */
    private static final List<String> STRINGS = strings();

    private static List<String> strings() {
        List<String> out = new ArrayList<>(List.of(
                "", "a", "b", "aa", "ab", "aaa", "x", "xx", "xxxx", "b1",
                "T1234567890123", "T123456789012", "T12345678901234",
                "12-345678", "12-34567", "1-345678",
                "01", "47", "48", "00", "39", "4", "007",
                "ｦ", "ｦｦ", "アー", "あ", "a@b.c", "a@b", "@b.c", "a b@c.d",
                "+81 90-1234-5678", "0312345678", "1",
                "006abcdefghijkl", "006abcdefghijklABC", "006abcdefghijklabc",
                "slug", "a-b-c", "a-", "-a", "A",
                "aab", "aaab", "ab", "0a ", "0a", " ",
                "a-", "-", "]", "]]", "é", "12", "1-", "--"));
        // The symbols a reading over units would get wrong, and the ones only Java's own list of
        // line terminators tells apart.
        out.add(new String(Character.toChars(0x10330)));
        out.add(new String(Character.toChars(0x10330)) + "a");
        out.add(new String(Character.toChars(0x10FFFF)));
        out.add("\ud800");
        out.add("\udc00");
        out.add("𐀀");
        for (int each : new int[] {'\n', '\r', 0x85, 0x2028, 0x2029, 0x0b, '\f', '\t'}) {
            out.add(String.valueOf((char) each));
        }
        return List.copyOf(out);
    }

    /** More than anything here asks for, unspent. A meter is spent as it is used, so each
     *  construction gets its own and what is measured is the language rather than the allowance. */
    private static Meter plenty() {
        return new Meter(100_000, 10_000_000);
    }

    @Test
    void everyPatternAcceptsWhatTheEngineAccepts() {
        List<String> apart = new ArrayList<>();
        for (String regex : PATTERNS) {
            PatternRead said = PatternParser.read(regex);
            PatternSyntax syntax =
                    assertInstanceOf(PatternRead.Read.class, said, regex).syntax();
            Automaton machine = Automaton.of(syntax, plenty());
            assertNotNull(machine, regex + " is small enough to build");

            java.util.regex.Pattern engine = java.util.regex.Pattern.compile(regex);
            for (String value : STRINGS) {
                boolean mine = machine.accepts(value);
                boolean theirs = engine.matcher(value).matches();
                if (mine != theirs) {
                    apart.add(regex + " over " + written(value)
                            + ": this says " + mine + ", the engine says " + theirs);
                }
            }
        }

        assertEquals(List.of(), apart);
    }

    /**
     * And the sample says something: every pattern refuses some of these and accepts some.
     *
     * <p>Without it the agreement above is one a machine accepting nothing would also reach, over
     * strings none of the patterns were ever going to take.
     */
    @Test
    void theStringsAskedAboutTellThePatternsApart() {
        for (String regex : PATTERNS) {
            java.util.regex.Pattern engine = java.util.regex.Pattern.compile(regex);
            long taken = STRINGS.stream().filter(each -> engine.matcher(each).matches()).count();

            assertTrue(taken > 0, regex + " accepts none of the strings asked about");
            assertTrue(taken < STRINGS.size(), regex + " accepts all of them");
        }
    }

    /**
     * A pattern past the states it was allowed is not built, and is not built smaller.
     *
     * <p>The bound is the caller's and the answer is that nothing was made. A machine of fewer
     * states accepts other strings, and handing one back would be this compiler answering a question
     * about a language with a language of its own.
     */
    @Test
    void aPatternPastWhatItWasAllowedIsNotBuilt() {
        PatternSyntax big = assertInstanceOf(PatternRead.Read.class,
                PatternParser.read("[0-9]{5000}")).syntax();

        org.junit.jupiter.api.Assertions.assertNull(Automaton.of(big, new Meter(100, 100)));
        assertNotNull(Automaton.of(big, plenty()), "and it is built where there is room");
    }

    private static String written(String value) {
        StringBuilder out = new StringBuilder("\"");
        value.codePoints().forEach(each -> out.append(each >= 0x20 && each < 0x7f
                ? String.valueOf((char) each) : String.format("\\u{%04X}", each)));
        return out.append('"').toString();
    }
}
