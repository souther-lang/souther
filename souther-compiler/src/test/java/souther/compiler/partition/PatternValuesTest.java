package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Optional;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A string the pattern an invariant states would accept.
 *
 * <p>Two things are being held to. What comes out has to match — which is checked here the way the
 * code checks it, by putting it back through the pattern, because a value that does not match is
 * refused at construction and reported as a combination the model rules out. And what comes out has to
 * be the same string every time: a generated block is read against the last one to see what changed,
 * and a value that varied between runs would make every row look changed.
 */
class PatternValuesTest {

    /** Every format rule written in `souther-lang/examples`, which is what this was built for. */
    private static final List<String> IN_THE_EXAMPLES = List.of(
            "[0-9]{6}",
            "[0-9]{2}-[0-9]{6}",
            "[0-9]{3}-[0-9]{4}",
            "[0-9]{12}",
            "[0-9]{13}",
            "[0-9]{16}",
            "[0-9]{4}",
            "[0-9][A-E]",
            "0[1-9]|[1-3][0-9]|4[0-7]",
            "[A-Z]{2}-[0-9]{4}",
            "[A-Z]{3}",
            "[A-Z]-[0-9]{2}-[0-9]{2}",
            "SH-[0-9]{6}",
            "RMA-[0-9]{8}",
            "INV-[0-9]{4}-[0-9]{6}",
            "FY[0-9]{2}-Q[1-4]",
            "T[0-9]{13}",
            "001",
            "003",
            "00Q",
            "006[0-9A-Za-z]{12}([0-9A-Z]{3})?",
            "00T[0-9A-Za-z]{12}([0-9A-Z]{3})?",
            "0Q0[0-9A-Za-z]{12}([0-9A-Z]{3})?",
            "[ｦ-ﾟァ-ヴー 　]+",
            "\\+?[0-9][0-9 \\-()]{6,19}",
            "[^@\\s]+@[^@\\s]+\\.[^@\\s]+",
            "[a-z0-9]([a-z0-9\\-]*[a-z0-9])?(\\.[a-z0-9]([a-z0-9\\-]*[a-z0-9])?)+");

    @Test
    void everyFormatRuleInTheExamplesGetsAValueThatMatches() {
        List<String> without = IN_THE_EXAMPLES.stream()
                .filter(regex -> PatternValues.shortestAccepted(regex).isEmpty()).toList();

        assertEquals(List.of(), without, "a format rule nothing can write a value for");
        for (String regex : IN_THE_EXAMPLES) {
            String value = PatternValues.shortestAccepted(regex).orElseThrow();
            assertTrue(Pattern.matches(regex, value), regex + " -> \"" + value + "\"");
        }
    }

    /** What it writes, so that a change to any of it is a change somebody decided on. */
    @Test
    void theValueIsTheShortestOneAndTheSameEveryTime() {
        assertEquals(Optional.of("00-000000"), PatternValues.shortestAccepted("[0-9]{2}-[0-9]{6}"));
        assertEquals(Optional.of("01"), PatternValues.shortestAccepted("0[1-9]|[1-3][0-9]|4[0-7]"),
                "the first branch of an alternation");
        assertEquals(Optional.of("006000000000000"),
                PatternValues.shortestAccepted("006[0-9A-Za-z]{12}([0-9A-Z]{3})?"),
                "an optional group is left out");
        assertEquals(Optional.of("0000000"),
                PatternValues.shortestAccepted("\\+?[0-9][0-9 \\-()]{6,19}"),
                "a bounded repetition takes its lower bound");
        assertEquals(Optional.of("a@a.a"),
                PatternValues.shortestAccepted("[^@\\s]+@[^@\\s]+\\.[^@\\s]+"),
                "a negated class takes a letter that is not excluded");
        assertEquals(Optional.of("ｦ"), PatternValues.shortestAccepted("[ｦ-ﾟァ-ヴー 　]+"),
                "a range is a range whatever alphabet it is in");
    }

    @Test
    void twoRunsOfOneRuleWriteTheSameValue() {
        for (String regex : IN_THE_EXAMPLES) {
            assertEquals(PatternValues.shortestAccepted(regex),
                    PatternValues.shortestAccepted(regex), regex);
        }
    }

    /**
     * An alphabet other than ASCII, on either side of a class.
     *
     * <p>A model here is as likely to state a rule in kana as in letters, and a rule that excludes
     * something is as likely to exclude ASCII as to exclude punctuation. Neither is a special case for
     * a reader that works in characters; what needed saying was where a negated class looks for one it
     * is allowed, which was letters and digits and nothing else.
     */
    @Test
    void aClassWrittenInAnotherAlphabetIsRead() {
        assertEquals(Optional.of("ぁ"), PatternValues.shortestAccepted("[ぁ-ん]+"));
        assertEquals(Optional.of("一一"), PatternValues.shortestAccepted("[一-龯]{2}"));
        assertEquals(Optional.of("ｦ"), PatternValues.shortestAccepted("[ｦ-ﾟ]"));

        assertEquals(Optional.of("a"), PatternValues.shortestAccepted("[^あいう]"),
                "a letter is not one of the three, so it is what a negated class takes");
        assertEquals(Optional.of("aaa"), PatternValues.shortestAccepted("[^あいう]{3}"));
    }

    /**
     * A negated class that leaves no letter or digit.
     *
     * <p>It had nothing to give: the characters it looked through were the alphanumerics, and a rule
     * excluding all of them is a rule asking for something else — punctuation, or a character outside
     * ASCII altogether. What it looks through now goes on past those.
     */
    @Test
    void aNegatedClassWithNoLetterLeftLooksFurther() {
        for (String regex : List.of("[^a-zA-Z0-9]", "[^a-zA-Z0-9 ]+", "[^ -~]", "[^\\x00-\\x7F]")) {
            String value = PatternValues.shortestAccepted(regex)
                    .orElseThrow(() -> new AssertionError("nothing written for " + regex));
            assertTrue(Pattern.matches(regex, value), regex + " -> \"" + value + "\"");
        }
        assertEquals(Optional.of("あ"), PatternValues.shortestAccepted("[^\\x00-\\x7F]"),
                "a rule excluding ASCII is asking for a character from somewhere else");
        assertEquals(Optional.of("あ"), PatternValues.shortestAccepted("[^ -~]+"),
                "and so is one excluding everything that prints in ASCII");
    }

    /**
     * A shorthand excludes everything it stands for.
     *
     * <p>What a member of a class puts in is a set, and the two questions a class is asked want
     * different amounts of it. One character is enough to be <em>in</em> the class. To be out of a
     * negated one, every character the member stands for has to be excluded — a reader that took only
     * the first of them excluded {@code a} and went on to offer {@code b}, which {@code [^\w]} refuses.
     */
    @Test
    void aShorthandInANegatedClassExcludesAllOfWhatItMeans() {
        for (String regex : List.of("[^\\w]+", "[^\\w\\s]", "[^\\d]", "[^\\s]", "[^0-9\\s]")) {
            String value = PatternValues.shortestAccepted(regex)
                    .orElseThrow(() -> new AssertionError("nothing written for " + regex));
            assertTrue(Pattern.matches(regex, value), regex + " -> \"" + value + "\"");
        }
        assertEquals(Optional.of("a"), PatternValues.shortestAccepted("[\\w]"),
                "and one character is still enough to be in the class");
        assertEquals(Optional.of("000"), PatternValues.shortestAccepted("[\\d]{3}"));
    }

    /**
     * A value a row could not carry is not a value.
     *
     * <p>What comes out is offered as text to paste into a model, as a string literal, on the line the
     * row is on. A character the literal cannot spell would go in as itself; a long enough one would go
     * in as a screenful. Both match the pattern and neither is something to hand anybody, so the answer
     * is the one for a pattern nothing can be written for.
     */
    @Test
    void aValueNoRowCanCarryIsNotOffered() {
        assertEquals(Optional.empty(), PatternValues.shortestAccepted("[^\\x00-\\uFFFF]"),
                "a rule leaving only characters a literal cannot spell");
        assertEquals(Optional.empty(), PatternValues.shortestAccepted("[0-9]{2000000}"),
                "a length nobody would read");
        assertEquals(Optional.empty(), PatternValues.shortestAccepted("a{2147483648}"),
                "a count past what a bound holds");

        assertEquals(Optional.of("\n"), PatternValues.shortestAccepted("\\n"),
                "and the ones a literal does spell are written");
    }

    /**
     * What it does not read, it does not guess at.
     *
     * <p>The alternative is a value that does not match, which is refused at construction and reported
     * as a combination the model rules out — a wrong answer where there was a missing one.
     */
    @Test
    void aRuleItCannotReadGetsNoValue() {
        List<String> beyondIt = List.of(
                "(a)\\1",            // a back reference
                "(?=x)y",            // a lookahead
                "(?<x>[0-9])",       // a named group
                "\\p{Alpha}+",       // a unicode property
                "[0-9",              // not a pattern at all
                "(a",
                "a{2,1}");           // a bound that admits nothing

        for (String regex : beyondIt) {
            assertEquals(Optional.empty(), PatternValues.shortestAccepted(regex), regex);
        }
    }

    /**
     * And the check that makes the rest of it safe.
     *
     * <p>Everything above is a construct someone thought about. What protects the ones nobody did is
     * that the answer goes back through the pattern before it is offered — so being wrong about a
     * construct produces nothing, which is what being unable to read it produces.
     */
    @Test
    void anythingItGetsWrongComesBackAsNothing() {
        // A quantifier this reads as "at least two" and the regex engine reads some other way would
        // still have to survive the pattern. Rather than a construct nobody has thought of, the case
        // is made with one whose meaning is genuinely elsewhere: possessive matching.
        for (String regex : List.of("a{2}+b", "[0-9]++", "(?:ab)*+c")) {
            Optional<String> value = PatternValues.shortestAccepted(regex);
            assertTrue(value.isEmpty() || Pattern.matches(regex, value.get()),
                    regex + " -> " + value);
        }
        assertFalse(PatternValues.shortestAccepted("[0-9]{2}").isEmpty(),
                "and an ordinary rule is still answered");
    }
}
