package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import souther.compiler.cst.CstParser;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * Laying a document out decides things its text does not record. A group written down the page
 * because it did not fit and one written down the page because it holds a forced break come out as
 * the same characters, and only one of them is a decision the width made.
 *
 * <p>This is what a reader of a difference needs and cannot get from the output: told that a line
 * broke, they still have to be told whether the canonical form would have kept it whole at another
 * width. Recovering that from the text means measuring the group again, which is running the layout
 * a second time and calling the answer evidence.
 */
class TheLayoutKeepsWhatItsTextCannotSayTest {

    /** Two documents laid out to one text, for two reasons. */
    @Test
    void aWidthBreakAndAForcedBreakWriteTheSameCharacters() {
        Doc tooWide = Doc.group(Doc.concat(Doc.text("ab"), Doc.LINE, Doc.text("cd")));
        Doc forced = Doc.group(Doc.concat(Doc.text("ab"), Doc.HARDLINE, Doc.text("cd")));

        Layout byWidth = tooWide.layout(4);
        Layout byForce = forced.layout(100);

        assertEquals("ab\ncd", byWidth.text());
        assertEquals(byWidth.text(), byForce.text(), "the two are one text");

        assertEquals(1, byWidth.decisions().size());
        assertEquals(1, byForce.decisions().size());
        assertNotEquals(
                byWidth.decisions().get(0).outcome(),
                byForce.decisions().get(0).outcome(),
                "the same text, and the layout says the two groups were laid out for"
                        + " different reasons");
    }

    /** And a group that fits says so, rather than saying nothing. */
    @Test
    void andAGroupThatFitsIsADecisionToo() {
        Doc fits = Doc.group(Doc.concat(Doc.text("ab"), Doc.LINE, Doc.text("cd")));

        Layout layout = fits.layout(100);

        assertEquals("ab cd", layout.text());
        assertEquals(1, layout.decisions().size());
    }

    /** Two groups written the same way are two decisions. A layout that kept them by their shape
     * would keep one, and the conditional-layout rule answers about a group rather than about a
     * kind of group. */
    @Test
    void andTwoGroupsWrittenTheSameWayAreTwoDecisions() {
        Doc one = Doc.group(Doc.concat(Doc.text("ab"), Doc.LINE, Doc.text("cd")));
        Doc other = Doc.group(Doc.concat(Doc.text("ab"), Doc.LINE, Doc.text("cd")));

        Layout layout = Doc.concat(one, Doc.HARDLINE, other).layout(100);

        assertEquals("ab cd\nab cd", layout.text());
        assertEquals(2, layout.decisions().size());
        assertEquals(2, layout.decisions().stream().map(GroupDecision::group).distinct().count(),
                "two groups, and the layout tells them apart");
    }

    /** The column a group was measured at is what the width was compared against, so it is the
     * layout's to say and not something a reader counts off the line. */
    @Test
    void andTheColumnAGroupWasMeasuredAtIsItsOwn() {
        Doc inner = Doc.group(Doc.concat(Doc.text("cd"), Doc.LINE, Doc.text("ef")));
        Layout layout = Doc.concat(Doc.text("ab "), inner).layout(100);

        assertEquals("ab cd ef", layout.text());
        assertEquals(List.of(3), layout.decisions().stream().map(GroupDecision::startColumn).toList());
    }

    /**
     * Every group of a document is one decision of its layout. Measuring a group walks ahead over
     * the groups inside it, and a layout that took a decision there would report the inner one twice
     * — once for having been considered and once for having been laid out.
     */
    @Test
    void everyGroupIsOneDecisionAndMeasuringTakesNone() {
        Doc inner = Doc.group(Doc.concat(Doc.text("cd"), Doc.LINE, Doc.text("ef")));
        Doc outer = Doc.group(Doc.concat(Doc.text("ab"), Doc.LINE, inner));

        Layout layout = outer.layout(100);

        assertEquals("ab cd ef", layout.text());
        assertEquals(2, layout.decisions().size(),
                "the outer group and the one inside it, and the inner one once");
    }

    /** A decision names the group that was laid out. Counting them agrees with a layout that
     * answered about a group it made up, which is why this reads the identities. */
    @Test
    void andADecisionNamesTheGroupThatWasLaidOut() {
        Doc inner = Doc.group(Doc.concat(Doc.text("cd"), Doc.LINE, Doc.text("ef")));
        Doc outer = Doc.group(Doc.concat(Doc.text("ab"), Doc.LINE, inner));

        List<Doc.GroupRef> laidOut = outer.layout(100).decisions().stream()
                .map(GroupDecision::group).toList();

        assertEquals(List.of(((Doc.Group) outer).ref(), ((Doc.Group) inner).ref()), laidOut,
                "the outer group and then the one inside it, each by its own identity");
    }

    /** And over a real source: the groups the document holds are the groups the layout decided
     * about, one for one. */
    @Test
    void andOverASourceTheyAreTheSameGroups() {
        for (String source : WhatGoesBetweenTwoTokensOnALineTest.corpus()) {
            Doc doc = Formatter.document(CstParser.parse(source).root()).resolve();
            List<Doc.GroupRef> written = new ArrayList<>();
            groupsOf(doc, written);
            List<Doc.GroupRef> decided = doc.layout(100).decisions().stream()
                    .map(GroupDecision::group).toList();
            assertEquals(written.size(), decided.size(),
                    "one decision per group, in:\n" + source);
            assertEquals(Set.copyOf(written), Set.copyOf(decided),
                    "and about those groups rather than about others, in:\n" + source);
        }
    }

    private static void groupsOf(Doc doc, List<Doc.GroupRef> out) {
        switch (doc) {
            case Doc.Group g -> {
                out.add(g.ref());
                groupsOf(g.doc(), out);
            }
            case Doc.Nest n -> groupsOf(n.doc(), out);
            case Doc.At a -> groupsOf(a.doc(), out);
            case Doc.Concat c -> c.parts().forEach(part -> groupsOf(part, out));
            default -> { }
        }
    }
}
