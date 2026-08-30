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

    private static PatternSyntax read(String regex) {
        PatternRead said = PatternParser.read(regex);
        return assertInstanceOf(PatternRead.Read.class, said, regex).syntax();
    }

    /** The strings {@code regex} accepts, which is where an anchor's answer shows. */
    private static Language accepted(String regex) {
        return PatternPlan.of(read(regex)).compile(PatternPlan.Budget.OF_ADMITTED_VALUES);
    }

    private static PatternRead.Unsupported refused(String regex) {
        PatternRead said = PatternParser.read(regex);
        return assertInstanceOf(PatternRead.NotRead.class, said, regex).why();
    }

    /** Every arm of a choice, not the first of them. */
    @Test
    void aChoiceKeepsEveryArm() {
        PatternSyntax.EitherOf said = assertInstanceOf(PatternSyntax.EitherOf.class,
                read("0[1-9]|[1-3][0-9]|4[0-7]"));

        assertEquals(3, said.arms().size(), said.toString());
    }

    /** And a choice of one arm is not a choice, so one written pattern has one tree. */
    @Test
    void aChoiceOfOneIsTheThingItself() {
        assertInstanceOf(PatternSyntax.Symbols.class, read("a"));
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
        PatternSyntax.Repeated some = assertInstanceOf(PatternSyntax.Repeated.class, read("a{2,6}"));
        assertEquals(2, some.least());
        assertEquals(6, some.most());
        assertFalse(some.unbounded());

        PatternSyntax.Repeated exactly =
                assertInstanceOf(PatternSyntax.Repeated.class, read("[0-9]{13}"));
        assertEquals(13, exactly.least());
        assertEquals(13, exactly.most());

        for (String each : List.of("a*", "a+", "a{2,}")) {
            assertTrue(assertInstanceOf(PatternSyntax.Repeated.class, read(each)).unbounded(), each);
        }
    }

    /**
     * A reluctant marker is about the walk, so the same language comes back; a possessive one is
     * not.
     *
     * <p>Reluctant takes as few copies as it can and takes more where the rest of the pattern needs
     * them, so what is matched whole is matched either way. Possessive takes what it can and gives
     * none of it back: {@code (?:|a)++} takes the empty string once and never tries again, and
     * accepts nothing the plain repetition accepts beyond it. Read as the plain one, this answered
     * for a wider language than the author wrote.
     */
    @Test
    void howAMatcherWalksIsNotPartOfWhatItAcceptsUnlessItGivesNothingBack() {
        assertEquals(read("a+"), read("a+?"));
        assertEquals(read("a{2,6}"), read("a{2,6}?"));

        assertEquals(PatternRead.Unsupported.A_POSSESSIVE_REPETITION, refused("a{2,6}+"));
        assertEquals(PatternRead.Unsupported.A_POSSESSIVE_REPETITION, refused("(?:|a)++"));
    }

    /**
     * What a negated class leaves, as a set.
     *
     * <p>Every symbol but the ones written, which is more than a reader choosing one value needs and
     * exactly what a language is. The supplementary symbols are in it: a reading over units would
     * hold the halves of one and refuse the character the engine accepts.
     */
    @Test
    void aNegatedClassLeavesEverythingElse() {
        CodePoints left = assertInstanceOf(PatternSyntax.Symbols.class, read("[^abc]")).held();

        assertFalse(left.has('a'));
        assertFalse(left.has('b'));
        assertFalse(left.has('c'));
        assertTrue(left.has('d'));
        assertTrue(left.has(0x10330), "a symbol past the basic plane is one of them");
        assertTrue(left.has('\n'), "a negated class does not leave out the line terminators");
        assertTrue(left.has(0xD800), "nor half of a pair, which the engine reads as one symbol");
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
        CodePoints left = assertInstanceOf(PatternSyntax.Symbols.class, read(".")).held();

        for (int each : new int[] {'\n', '\r', 0x85, 0x2028, 0x2029}) {
            assertFalse(left.has(each), "U+" + String.format("%04X", each));
        }
        assertTrue(left.has(' '));
        assertTrue(left.has(0x10330));
        assertTrue(left.has(0xD800));
        assertEquals(CodePoints.EVERYTHING.size() - 5, left.size());
    }

    /** A symbol past the basic plane is one symbol, written out or as a number. */
    @Test
    void aSymbolPastTheBasicPlaneIsOne() {
        String gothic = new String(Character.toChars(0x10330));

        assertEquals(CodePoints.of(0x10330),
                assertInstanceOf(PatternSyntax.Symbols.class, read(gothic)).held());
        assertEquals(CodePoints.of(0x10330),
                assertInstanceOf(PatternSyntax.Symbols.class, read("\\x{10330}")).held());
        assertEquals(CodePoints.between(0x10000, 0x10400),
                assertInstanceOf(PatternSyntax.Symbols.class,
                        read("[\\x{10000}-\\x{10400}]")).held());
    }

    /** The shorthands hold what Java holds them to without a flag. */
    @Test
    void theShorthandsAreTheOnesJavaHasWithoutAFlag() {
        CodePoints digits = assertInstanceOf(PatternSyntax.Symbols.class, read("\\d")).held();
        assertEquals(CodePoints.between('0', '9'), digits);
        assertFalse(digits.has('０'), "a fullwidth digit is not one of them");

        CodePoints word = assertInstanceOf(PatternSyntax.Symbols.class, read("\\w")).held();
        assertTrue(word.has('_'));
        assertFalse(word.has(0x10330));

        assertEquals(assertInstanceOf(PatternSyntax.Symbols.class, read("\\D")).held(),
                digits.not(), "the capital is what the small one leaves");
    }

    /**
     * An anchor says where a match sits, and what that comes to is not the anchor's own.
     *
     * <p>Kept in the tree, because the answer is settled by where it stands: at the edge it asks
     * for nothing, and after something that must take a symbol it asks for a position no string
     * has. Read as adding nothing wherever it appeared, {@code a^b} was accepted as {@code ab}.
     */
    @Test
    void anAnchorIsKeptAndWhatItComesToIsReadFromWhereItStands() {
        assertEquals(new PatternSyntax.Anchor(false), read("^"));
        assertInstanceOf(PatternSyntax.InTurn.class, read("^abc$"),
                "the anchors are still in the tree");

        assertEquals(accepted("abc"), accepted("^abc$"),
                "at the edges they ask for nothing");
        assertTrue(accepted("a^b").isEmpty(),
                "no position is both after an a and at the start, so no string is accepted");
        assertEquals(accepted("a"), accepted("^a$|a^b"),
                "an arm nothing satisfies leaves the choice its other arms");
    }

    /** A pattern whose anchor has no answer is not read at all. */
    @Test
    void anAnchorWhosePlaceIsNotSettledIsRefused() {
        assertEquals(PatternRead.Unsupported.AN_ANCHOR_THIS_CANNOT_PLACE, refused("(a|)^b"),
                "what is before it sometimes takes a symbol and sometimes does not");
        assertEquals(PatternRead.Unsupported.AN_ANCHOR_THIS_CANNOT_PLACE, refused("(^a)*"),
                "how many copies come before it is the string's answer and not the pattern's");
        // And `$` away from the end is not the mirror of `^` away from the start. It is satisfied
        // just before a line terminator that ends the string as well as at the end itself, so
        // `a$b` is not a pattern nothing satisfies — it is one this has no shape for.
        assertEquals(PatternRead.Unsupported.AN_ANCHOR_THIS_CANNOT_PLACE, refused("a$b"),
                "the end of a string is not the only place the engine puts it");
    }

    /** Every construct outside the subset is refused, and says which it was. */
    @Test
    void whatIsOutsideTheSubsetIsRefusedAndNamed() {
        assertEquals(PatternRead.Unsupported.A_GROUP_ABOUT_THE_MATCH, refused("(?=a)b"));
        assertEquals(PatternRead.Unsupported.A_GROUP_ABOUT_THE_MATCH, refused("(?<name>a)"));
        assertEquals(PatternRead.Unsupported.A_GROUP_ABOUT_THE_MATCH, refused("(?i)a"));
        assertEquals(PatternRead.Unsupported.A_BACK_REFERENCE, refused("(a)\\1"));
        assertEquals(PatternRead.Unsupported.A_BACK_REFERENCE, refused("\\k<a>"));
        assertEquals(PatternRead.Unsupported.A_CHARACTER_PROPERTY, refused("\\p{Alpha}"));
        assertEquals(PatternRead.Unsupported.A_BOUNDARY, refused("\\bword\\b"));
        assertEquals(PatternRead.Unsupported.A_QUOTATION, refused("\\Qa+b\\E"));
        assertEquals(PatternRead.Unsupported.A_CLASS_OF_CLASSES, refused("[a-z&&[^bc]]"));
        assertEquals(PatternRead.Unsupported.SOMETHING_UNCLOSED, refused("(a"));
        assertEquals(PatternRead.Unsupported.SOMETHING_UNCLOSED, refused("[a"));
        assertEquals(PatternRead.Unsupported.SOMETHING_UNCLOSED, refused("a)"));
        assertEquals(PatternRead.Unsupported.AN_ESCAPE_THIS_DOES_NOT_READ, refused("\\y"));
        assertEquals(PatternRead.Unsupported.A_COUNT_THIS_CANNOT_READ, refused("a{6,2}"));
        assertEquals(PatternRead.Unsupported.A_COUNT_THIS_CANNOT_READ, refused("a{99999999999}"));
    }

    /**
     * A pattern outside the subset is refused whole, and never read in part.
     *
     * <p>What a reading of the part it understood would hold is a language narrower than the rule,
     * and every value the author meant would go on being accepted by it. So the answer is that the
     * pattern was not read.
     */
    @Test
    void aPatternIsReadWholeOrNotAtAll() {
        assertInstanceOf(PatternRead.NotRead.class, PatternParser.read("[0-9]{3}\\p{Alpha}"));
        assertInstanceOf(PatternRead.NotRead.class, PatternParser.read("(a)\\1[0-9]"));
    }

    /** Written more deeply than the reading goes is a limit of the reading, and it says so rather
     *  than falling over. */
    @Test
    void aPatternNestedPastTheReadingSaysSo() {
        assertEquals(PatternRead.Unsupported.NESTED_TOO_DEEPLY,
                refused("(?:".repeat(500) + "a" + ")".repeat(500)));
    }
}
