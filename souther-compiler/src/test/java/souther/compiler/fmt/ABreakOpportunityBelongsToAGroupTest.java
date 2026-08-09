package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A place the layout may break belongs to the group whose decision settles it.
 *
 * <p>The conditional-layout rule answers about a group, and a deviation from it is a source that
 * broke where the canonical form does not or kept whole what it breaks. Saying which of the two
 * needs the group that decided, and where the canonical form is flat there is no break to have been
 * decided — nothing the layout wrote points at the group. So what a source gap is matched against
 * is the opportunity, which is there either way.
 */
class ABreakOpportunityBelongsToAGroupTest {

    /** A group that fits: its opportunities are there, and none of them was written as a break. */
    @Test
    void aFlatGroupStillHasItsOpportunities() {
        Doc doc = Doc.group(Doc.concat(Doc.text("ab"), Doc.line(), Doc.text("cd")));

        Layout layout = doc.layout(100);

        assertEquals("ab cd", layout.text());
        assertEquals(1, layout.opportunities().size());
        assertEquals(false, layout.opportunities().get(0).broke());
    }

    /** And the same group over the width breaks at the same opportunity. */
    @Test
    void andTheSameGroupTooWideBreaksAtIt() {
        Doc doc = Doc.group(Doc.concat(Doc.text("ab"), Doc.line(), Doc.text("cd")));

        Layout layout = doc.layout(4);

        assertEquals("ab\ncd", layout.text());
        assertEquals(1, layout.opportunities().size());
        assertEquals(true, layout.opportunities().get(0).broke());
    }

    /** An opportunity names the group that settled it, and that is the decision explaining it. */
    @Test
    void andItNamesTheGroupThatSettledIt() {
        Doc inner = Doc.group(Doc.concat(Doc.text("ab"), Doc.line(), Doc.text("cd")));
        Doc outer = Doc.group(Doc.concat(Doc.text("x"), Doc.line(), inner));

        Layout layout = outer.layout(100);

        assertEquals("x ab cd", layout.text());
        assertEquals(2, layout.opportunities().size());
        List<Doc.GroupRef> settling = layout.opportunities().stream()
                .map(Opportunity::settledBy).toList();
        assertEquals(List.of(((Doc.Group) outer).ref(), ((Doc.Group) inner).ref()), settling,
                "the outer group's own, then the one inside it — the innermost group holding it");
    }

    /** And the decision it names is in the layout, so a reader goes from the opportunity to why. */
    @Test
    void andThatGroupsDecisionIsThere() {
        Doc doc = Doc.group(Doc.concat(Doc.text("ab"), Doc.line(), Doc.text("cd")));

        Layout layout = doc.layout(4);
        Opportunity broke = layout.opportunities().get(0);

        assertTrue(layout.decisions().stream().anyMatch(d -> d.group() == broke.settledBy()),
                "the group that settled it decided, and the decision says why");
    }

    /** Every boundary the layout may break is one opportunity, over a real source. */
    @Test
    void andOverASourceEveryOneIsThere() {
        for (String source : WhatGoesBetweenTwoTokensOnALineTest.corpus()) {
            Doc doc = Formatter.canonicalize(
                    souther.compiler.cst.CstParser.parse(source).root()).construction().doc()
                    .resolve();
            long lines = linesIn(doc);
            assertEquals(lines, doc.layout(100).opportunities().size(),
                    "one opportunity per boundary the layout may break, in:\n" + source);
        }
    }

    private static long linesIn(Doc doc) {
        return switch (doc) {
            case Doc.Line _ -> 1;
            case Doc.Group g -> linesIn(g.doc());
            case Doc.Nest n -> linesIn(n.doc());
            case Doc.At a -> linesIn(a.doc());
            case Doc.Concat c -> c.parts().stream().mapToLong(ABreakOpportunityBelongsToAGroupTest::linesIn).sum();
            default -> 0;
        };
    }

    /**
     * Two places written the same way are two opportunities. Read by their shape they would be one,
     * and a witness naming one of them would be naming both.
     */
    @Test
    void andTwoWrittenTheSameWayAreTwo() {
        Doc doc = Doc.group(Doc.concat(
                Doc.text("ab"), Doc.line(), Doc.text("cd"), Doc.line(), Doc.text("ef")));

        List<Opportunity> found = doc.layout(100).opportunities();

        assertEquals(2, found.size());
        assertNotSame(found.get(0).line(), found.get(1).line(),
                "each is its own, and neither stands for the other");
    }
}
