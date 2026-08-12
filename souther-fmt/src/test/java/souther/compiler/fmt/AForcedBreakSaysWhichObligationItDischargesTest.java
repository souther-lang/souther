package souther.compiler.fmt;

import org.junit.jupiter.api.Test;
import souther.compiler.cst.CstParser;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A break written whatever the width says which obligation it discharges.
 *
 * <p>{@link AForcedBreakIsWrittenWhateverTheWidthTest} holds that each of them is written. This
 * holds that the layout says which one — the difference being that a reader of the first has the
 * text and has to know the rules to read a break out of it, and a reader of this is told.
 *
 * <p>The obligation is named where the boundary is built and carried to the break. A test that read
 * it back off the text would be the walk the naming is here to remove: the characters of a break
 * written because a construct writes its members one to a line and one written because a comment
 * cannot share its line are the same character.
 */
class AForcedBreakSaysWhichObligationItDischargesTest {

    private static final String MEMBERS = """
            module fmtprobe exposing ( f )

            let f (x: Int): Int =
                {
                    let a = x
                    a
                }
            """;

    private static final String ITEMS = """
            module fmtprobe exposing ( Alpha, Beta )

            data Alpha = Int

            data Beta = Int
            """;

    private static final String COMMENTED = """
            module fmtprobe exposing ( Alpha )

            // what it is for
            data Alpha = Int
            """;

    private static final String FIELDS = """
            module fmtprobe exposing ( P )

            data P =
                { alpha: Int
                , beta: Int
                }
            """;

    /** A construct written down the page writes each member on a line of its own, and each of the
     * breaks that does it says so. */
    @Test
    void aMemberOnALineOfItsOwnSaysItIsThat() {
        assertEquals(Obligation.MEMBERS_TAKE_LINES_OF_THEIR_OWN, endingTheLine(MEMBERS, "let a = x"),
                "the break after a statement of a block is the one that keeps the next on its own"
                        + " line");
        assertEquals(Obligation.MEMBERS_TAKE_LINES_OF_THEIR_OWN,
                endingTheLine(FIELDS, "{ alpha: Int"));
    }

    /** The bracket that closes a construct written down the page takes a line of its own, and the
     * break in front of it is not the one that separated the members. */
    @Test
    void aClosingBracketSaysItIsABracket() {
        assertEquals(Obligation.A_BRACKET_TAKES_A_LINE_OF_ITS_OWN, endingTheLine(MEMBERS, "a"),
                "the break before `}` closes the block rather than separating two statements");
        assertEquals(Obligation.A_BRACKET_TAKES_A_LINE_OF_ITS_OWN,
                endingTheLine(FIELDS, ", beta: Int"));
    }

    /** The last break of a file is the file's own, and no construct's. */
    @Test
    void theLastBreakOfAFileSaysItIsTheFiles() {
        Layout layout = layoutOf(ITEMS);
        List<Newline> breaks = layout.breaks();
        assertEquals(new Newline.Cause.Forced(Obligation.A_FILE_ENDS_WITH_ONE_NEWLINE),
                breaks.get(breaks.size() - 1).cause());
        assertEquals(1, causes(layout).stream()
                .filter(Obligation.A_FILE_ENDS_WITH_ONE_NEWLINE::equals).count(),
                "one file, one break that ends it");
    }

    /**
     * A blank line between two items is two breaks at one adjacency, and the separation rule is one
     * of them.
     *
     * <p>Asserted over the pair rather than over either break. What the rule says is that a blank
     * line stands between the two items; which of the two newline characters is the blank one is
     * not something it says, so a test naming one of them would be holding the formatter to an
     * order the rule does not have.
     */
    @Test
    void theBlankLineBetweenTwoItemsSaysItSeparatesThem() {
        Layout layout = layoutOf(ITEMS);
        String text = layout.text();
        List<Obligation> atTheGap = new ArrayList<>();
        for (Newline n : layout.breaks()) {
            if (lineEndingAt(text, n).equals("data Alpha = Int") || blankLineEndingAt(text, n)) {
                if (n.cause() instanceof Newline.Cause.Forced f) {
                    atTheGap.add(f.obligation());
                }
            }
        }
        assertTrue(atTheGap.contains(Obligation.A_BLANK_LINE_SEPARATES_TOP_LEVEL_ITEMS),
                "the two breaks between the items are " + atTheGap);
        assertTrue(atTheGap.contains(Obligation.MEMBERS_TAKE_LINES_OF_THEIR_OWN),
                "the second of them opens the next item's line: " + atTheGap);
    }

    /** Nothing is written after a comment on its line, and the break that holds to it says so
     * rather than being read as the item separation it sits next to. */
    @Test
    void theBreakAfterACommentSaysItIsTheCommentsLine() {
        assertEquals(Obligation.NOTHING_SHARES_A_COMMENTS_LINE,
                endingTheLine(COMMENTED, "// what it is for"));
    }

    /** Every obligation is one some source reaches. An obligation no construction writes would be
     * a name in the enum and nothing in the canonical form. */
    @Test
    void everyObligationIsOneSomethingIsWrittenFor() {
        Set<Obligation> found = EnumSet.noneOf(Obligation.class);
        for (String source : List.of(MEMBERS, ITEMS, COMMENTED, FIELDS)) {
            found.addAll(causes(layoutOf(source)));
        }
        assertEquals(EnumSet.allOf(Obligation.class), found);
    }

    /** A break the width settled is not one of these. The two are told apart by what the layout
     * holds and not by the characters, which are the same. */
    @Test
    void aBreakAGroupSettledNamesNoObligation() {
        Doc doc = Doc.group(Doc.concat(Doc.text("ab"), Doc.line(), Doc.text("cd")));

        Newline wrote = doc.layout(4).breaks().get(0);

        assertTrue(wrote.cause() instanceof Newline.Cause.Settled,
                "a break the group settled points at the opportunity, not at an obligation");
    }

    private static Layout layoutOf(String source) {
        return Formatter.canonicalize(CstParser.parse(source).root()).layout();
    }

    /** The obligations of the forced breaks a layout wrote. */
    private static List<Obligation> causes(Layout layout) {
        List<Obligation> out = new ArrayList<>();
        for (Newline n : layout.breaks()) {
            if (n.cause() instanceof Newline.Cause.Forced f) {
                out.add(f.obligation());
            }
        }
        return out;
    }

    /** The obligation of the break that ends the line reading {@code line}. */
    private static Obligation endingTheLine(String source, String line) {
        Layout layout = layoutOf(source);
        String text = layout.text();
        List<Obligation> found = new ArrayList<>();
        for (Newline n : layout.breaks()) {
            if (lineEndingAt(text, n).equals(line) && n.cause() instanceof Newline.Cause.Forced f) {
                found.add(f.obligation());
            }
        }
        assertEquals(1, found.size(),
                found.size() + " forced breaks end a line reading `" + line + "` in:\n" + text);
        return found.get(0);
    }

    /** What is written on the line the break at {@code n} ends, without its indent. */
    private static String lineEndingAt(String text, Newline n) {
        return text.substring(text.lastIndexOf('\n', n.offset() - 1) + 1, n.offset()).strip();
    }

    private static boolean blankLineEndingAt(String text, Newline n) {
        return lineEndingAt(text, n).isEmpty() && n.offset() > 0;
    }
}
