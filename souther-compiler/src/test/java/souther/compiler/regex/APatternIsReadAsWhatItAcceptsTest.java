package souther.compiler.regex;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A pattern is read as what it accepts, and nothing it says is dropped on the way.
 *
 * <p>A reading of a pattern that keeps less than the pattern says answers for a narrower language,
 * and that is the direction nothing catches: a narrower set still holds the values somebody wrote,
 * so every row goes on being accepted and the answer is quietly wrong. The three places it is easy
 * to lose something are the arms of a choice, the ceiling of a repetition, and what a negated class
 * leaves — so those are what this is about.
 */
class APatternIsReadAsWhatItAcceptsTest {

    private static PatternMeaning read(String regex) {
        PatternRead said = PatternParser.read(regex);
        return assertInstanceOf(PatternRead.Read.class, said, regex).meaning();
    }

    /** The strings {@code regex} accepts, which is where an anchor's answer shows. */
    private static Language accepted(String regex) {
        return PatternPlan.of(read(regex)).compile(PatternPlan.Budget.OF_ADMITTED_VALUES.meter());
    }

    private static PatternRead.Refused refusal(String regex) {
        return assertInstanceOf(PatternRead.Refused.class, PatternParser.read(regex), regex);
    }

    private static PatternRead.Refusal refused(String regex) {
        return refusal(regex).why();
    }

    /** Every arm of a choice, not the first of them. */
    @Test
    void aChoiceKeepsEveryArm() {
        PatternMeaning.EitherOf said = assertInstanceOf(PatternMeaning.EitherOf.class,
                read("0[1-9]|[1-3][0-9]|4[0-7]"));

        assertEquals(3, said.arms().size(), said.toString());
    }

    /** And a choice of one arm is not a choice, so one written pattern has one tree. */
    @Test
    void aChoiceOfOneIsTheThingItself() {
        assertInstanceOf(PatternMeaning.Symbols.class, read("a"));
    }

    /**
     * Both ends of a repetition.
     *
     * <p>The ceiling is what a reading built to choose one value has no use for and drops. Held as
     * the floor alone, `{2,6}` accepts the strings of length two and the language leaves out four
     * lengths the author wrote.
     */
    @Test
    void aRepetitionKeepsItsCeiling() {
        PatternMeaning.Repeated some = assertInstanceOf(PatternMeaning.Repeated.class, read("a{2,6}"));
        assertEquals(2, some.least());
        assertEquals(6, some.most());
        assertFalse(some.unbounded());

        PatternMeaning.Repeated exactly =
                assertInstanceOf(PatternMeaning.Repeated.class, read("[0-9]{13}"));
        assertEquals(13, exactly.least());
        assertEquals(13, exactly.most());

        for (String each : List.of("a*", "a+", "a{2,}")) {
            assertTrue(assertInstanceOf(PatternMeaning.Repeated.class, read(each)).unbounded(), each);
        }
    }

    /**
     * A reluctant marker is about the walk, so the same language comes back; a possessive one is
     * not.
     *
     * <p>Reluctant takes as few copies as it can and takes more where the rest of the pattern needs
     * them, so what is matched whole is matched either way. Possessive takes what it can and gives
     * none of it back: {@code (?:|a)++} takes the empty string once and never tries again, and
     * accepts nothing the plain repetition accepts beyond it. Which strings it accepts is a fact
     * about a matcher, and the language has no matcher in it.
     */
    @Test
    void howAMatcherWalksIsNotPartOfWhatItAcceptsUnlessItGivesNothingBack() {
        assertEquals(read("a+"), read("a+?"));
        assertEquals(read("a{2,6}"), read("a{2,6}?"));

        assertEquals(PatternRead.Refusal.A_POSSESSIVE_REPETITION, refused("a{2,6}+"));
        assertEquals(PatternRead.Refusal.A_POSSESSIVE_REPETITION, refused("(?:|a)++"));
    }

    /**
     * What a negated class leaves, as a set.
     *
     * <p>Every symbol but the ones written, which is more than a reader choosing one value needs and
     * exactly what a language is. The supplementary symbols are in it: a reading over units would
     * hold the halves of one and refuse the character.
     */
    @Test
    void aNegatedClassLeavesEverythingElse() {
        CodePoints left = assertInstanceOf(PatternMeaning.Symbols.class, read("[^abc]")).held();

        assertFalse(left.has('a'));
        assertFalse(left.has('b'));
        assertFalse(left.has('c'));
        assertTrue(left.has('d'));
        assertTrue(left.has(0x10330), "a symbol past the basic plane is one of them");
        assertTrue(left.has('\n'), "a negated class does not leave out the line terminators");
        assertFalse(left.has(0xD800), "half of a pair is no character, so no class holds one");
        assertEquals(CodePoints.EVERYTHING.size() - 3, left.size());
    }

    /**
     * And what `.` leaves, which is not the same thing.
     *
     * <p>Five line terminators and no others. Written as its own difference rather than as a rule,
     * so that a negated class beside it — which leaves them in — is the same algebra over another
     * set.
     */
    @Test
    void aDotLeavesOutTheFiveLineTerminators() {
        CodePoints left = assertInstanceOf(PatternMeaning.Symbols.class, read(".")).held();

        for (int each : new int[] {'\n', '\r', 0x85, 0x2028, 0x2029}) {
            assertFalse(left.has(each), "U+" + String.format("%04X", each));
        }
        assertTrue(left.has(' '));
        assertTrue(left.has(0x10330));
        assertFalse(left.has(0xD800));
        assertEquals(CodePoints.EVERYTHING.size() - 5, left.size());
    }

    /** A symbol past the basic plane is one symbol, written out or as a number. */
    @Test
    void aSymbolPastTheBasicPlaneIsOne() {
        String gothic = new String(Character.toChars(0x10330));

        assertEquals(CodePoints.of(0x10330),
                assertInstanceOf(PatternMeaning.Symbols.class, read(gothic)).held());
        assertEquals(CodePoints.of(0x10330),
                assertInstanceOf(PatternMeaning.Symbols.class, read("\\x{10330}")).held());
        assertEquals(CodePoints.between(0x10000, 0x10400),
                assertInstanceOf(PatternMeaning.Symbols.class,
                        read("[\\x{10000}-\\x{10400}]")).held());
    }

    /** The shorthands hold the sets the specification states, ASCII all of them. */
    @Test
    void theShorthandsAreTheSetsTheLanguageStates() {
        CodePoints digits = assertInstanceOf(PatternMeaning.Symbols.class, read("\\d")).held();
        assertEquals(CodePoints.between('0', '9'), digits);
        assertFalse(digits.has('０'), "a fullwidth digit is not one of them");

        CodePoints word = assertInstanceOf(PatternMeaning.Symbols.class, read("\\w")).held();
        assertTrue(word.has('_'));
        assertFalse(word.has(0x10330));

        CodePoints spaces = assertInstanceOf(PatternMeaning.Symbols.class, read("\\s")).held();
        assertEquals(6, spaces.size());
        assertFalse(spaces.has(0x3000), "an ideographic space is String whitespace and not this");

        assertEquals(assertInstanceOf(PatternMeaning.Symbols.class, read("\\D")).held(),
                digits.not(), "the capital is what the small one leaves");
    }

    /**
     * An anchor says where a match sits, and what that comes to is settled where the pattern is
     * read.
     *
     * <p>At the edge it asks for nothing, and after something that must take a symbol it asks for a
     * position no string has. Read as adding nothing wherever it appeared, {@code a^b} was accepted
     * as {@code ab}. What comes out of the reader holds none: nothing past it is asked again.
     */
    @Test
    void anAnchorIsReadAsWhatItComesToWhereItStands() {
        assertEquals(new PatternMeaning.Nothing(), read("^"));
        assertEquals(read("abc"), read("^abc$"), "at the edges they ask for nothing");

        assertTrue(accepted("a^b").isEmpty(),
                "no position is both after an a and at the start, so no string is accepted");
        assertEquals(accepted("a"), accepted("^a$|a^b"),
                "an arm nothing satisfies leaves the choice its other arms");
        assertEquals(accepted("a|b"), accepted("(^a|b$)"),
                "an anchor inside a choice at the edge asks for nothing either");
    }

    /** A pattern whose anchor has no answer is refused. */
    @Test
    void anAnchorWhosePlaceIsNotSettledIsRefused() {
        assertEquals(PatternRead.Refusal.AN_ANCHOR_THIS_CANNOT_PLACE, refused("(a|)^b"),
                "what is before it sometimes takes a symbol and sometimes does not");
        assertEquals(PatternRead.Refusal.AN_ANCHOR_THIS_CANNOT_PLACE, refused("(^a)*"),
                "how many copies come before it is the string's answer and not the pattern's");
        // And `$` away from the end is not the mirror of `^` away from the start. It is satisfied
        // just before a line terminator that ends the string as well as at the end itself, so
        // `a$b` is not a pattern nothing satisfies — it is one the language has no shape for.
        assertEquals(PatternRead.Refusal.AN_ANCHOR_THIS_CANNOT_PLACE, refused("a$b"),
                "the end of a string is not the only place a `$` is satisfied");
    }

    /** Every construct the language does not have is refused, and says which it was. */
    @Test
    void whatTheLanguageDoesNotHaveIsRefusedAndNamed() {
        assertEquals(PatternRead.Refusal.A_GROUP_ABOUT_THE_MATCH, refused("(?=a)b"));
        assertEquals(PatternRead.Refusal.A_GROUP_ABOUT_THE_MATCH, refused("(?<name>a)"));
        assertEquals(PatternRead.Refusal.A_GROUP_ABOUT_THE_MATCH, refused("(?i)a"));
        assertEquals(PatternRead.Refusal.A_BACK_REFERENCE, refused("(a)\\1"));
        assertEquals(PatternRead.Refusal.A_BACK_REFERENCE, refused("\\k<a>"));
        assertEquals(PatternRead.Refusal.A_CHARACTER_PROPERTY, refused("\\p{Alpha}"));
        assertEquals(PatternRead.Refusal.A_BOUNDARY, refused("\\bword\\b"));
        assertEquals(PatternRead.Refusal.A_QUOTATION, refused("\\Qa+b\\E"));
        assertEquals(PatternRead.Refusal.A_CLASS_OF_CLASSES, refused("[a-z&&[^bc]]"));
        assertEquals(PatternRead.Refusal.A_CLASS_OF_CLASSES, refused("[a[bc]]"));
        assertEquals(PatternRead.Refusal.SOMETHING_UNCLOSED, refused("(a"));
        assertEquals(PatternRead.Refusal.SOMETHING_UNCLOSED, refused("[a"));
        assertEquals(PatternRead.Refusal.SOMETHING_UNCLOSED, refused("a)"));
        assertEquals(PatternRead.Refusal.SOMETHING_UNCLOSED, refused("*a"));
        assertEquals(PatternRead.Refusal.AN_ESCAPE_THIS_DOES_NOT_READ, refused("\\y"));
        assertEquals(PatternRead.Refusal.A_COUNT_THIS_CANNOT_READ, refused("a{6,2}"));
        assertEquals(PatternRead.Refusal.A_COUNT_THIS_CANNOT_READ, refused("a{99999999999}"));
        assertEquals(PatternRead.Refusal.A_COUNT_THIS_CANNOT_READ, refused("a{"));
    }

    /**
     * A refusal quotes what stopped it, from where that construct begins.
     *
     * <p>What an author is shown is the construct and not the pattern: a lookahead in the middle of
     * a long format is found by what it is, and a pattern that ended before it was closed has no
     * construct to show.
     */
    @Test
    void aRefusalQuotesTheConstructThatStoppedIt() {
        assertEquals("(?=", refusal("[0-9]{3}(?=a)").construct());
        assertEquals("\\p", refusal("a\\p{Alpha}").construct());
        assertEquals("\\1", refusal("(a)\\1").construct());
        assertEquals("++", refusal("a++").construct());
        assertEquals("&&", refusal("[a-z&&b]").construct());
        assertEquals("\\uD800", refusal("x\\uD800").construct());
        assertEquals(1, refusal("x\\uD800").from());
        assertEquals("", refusal("(ab").construct(), "the text ended where a `)` was wanted");
    }

    /**
     * A pattern the language does not have is refused whole, and never read in part.
     *
     * <p>What a reading of the part it understood would hold is a language narrower than the rule,
     * and every value the author meant would go on being accepted by it.
     */
    @Test
    void aPatternIsReadWholeOrNotAtAll() {
        assertInstanceOf(PatternRead.Refused.class, PatternParser.read("[0-9]{3}\\p{Alpha}"));
        assertInstanceOf(PatternRead.Refused.class, PatternParser.read("(a)\\1[0-9]"));
    }

    /** Written more deeply than the compiler reads is a limit of the compiler, and it says so
     *  rather than falling over — and not as a refusal, since every construct in it is one the
     *  language has. */
    @Test
    void aPatternNestedPastTheReadingSaysSo() {
        assertEquals(new PatternRead.TooDeep(PatternParser.DEEPEST),
                PatternParser.read("(?:".repeat(500) + "a" + ")".repeat(500)));
        assertInstanceOf(PatternRead.Read.class, PatternParser.read(
                "(?:".repeat(PatternParser.DEEPEST) + "a" + ")".repeat(PatternParser.DEEPEST)));
    }
}
