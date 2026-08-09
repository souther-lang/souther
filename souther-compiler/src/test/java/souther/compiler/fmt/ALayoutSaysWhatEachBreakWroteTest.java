package souther.compiler.fmt;

import org.junit.jupiter.api.Test;

import souther.compiler.cst.CstParser;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotSame;

/**
 * A break is a decision and the layout keeps it: where it was written, how far in, and which
 * nesting it was written under.
 *
 * <p>Two of the fourteen rules ask about this and neither can be answered from the document. The
 * indentation rule asks about a pair of consecutive nesting levels, so a written indent of eight on
 * its own leaves the pair to be worked out from the text. And a blank line is two breaks at one
 * adjacency — {@link Gaps#boundaries} shows one boundary there, so what the top-level separation
 * rule decided is a canonical fact the document's view cannot show.
 */
class ALayoutSaysWhatEachBreakWroteTest {

    /** A blank line is two breaks and comes back as two. */
    @Test
    void aBlankLineIsTwoBreaks() {
        Layout layout = Formatter.canonicalize(CstParser.parse("""
                module m

                data A

                data B
                """).root()).layout();

        List<Integer> offsets = layout.breaks().stream().map(Newline::offset).toList();
        String text = layout.text();
        assertEquals("module m\n\ndata A\n\ndata B\n", text);
        assertEquals(List.of(8, 9, 16, 17, 24), offsets,
                "each newline the layout wrote, and the two of a blank line are both there");
    }

    /** A break says how far in it was written and which nesting wrote it. */
    @Test
    void andABreakSaysWhichNestingItWasWrittenUnder() {
        Doc inner = Doc.nest(4, Doc.concat(Doc.text("a"), Doc.hardline(), Doc.text("b")));
        Layout layout = Doc.group(inner).layout(100);

        assertEquals("a\n    b", layout.text());
        assertEquals(1, layout.breaks().size());
        Newline wrote = layout.breaks().get(0);
        assertEquals(4, wrote.indent());
        assertEquals(List.of(((Doc.Nest) inner).ref()), wrote.under(),
                "the nesting it was written under, by that nesting's own identity");
    }

    /** Two nestings written the same way are two, so the pair of levels a break sits between is
     * readable rather than guessed from the amounts. */
    @Test
    void andConsecutiveLevelsAreTellableApart() {
        Doc innermost = Doc.nest(4, Doc.concat(Doc.text("b"), Doc.hardline(), Doc.text("c")));
        Doc outer = Doc.nest(4, Doc.concat(Doc.text("a"), Doc.hardline(), innermost));
        Layout layout = Doc.group(outer).layout(100);

        assertEquals("a\n    b\n        c", layout.text());
        assertEquals(List.of(4, 8), layout.breaks().stream().map(Newline::indent).toList());

        List<Doc.NestRef> shallower = layout.breaks().get(0).under();
        List<Doc.NestRef> deeper = layout.breaks().get(1).under();
        assertEquals(1, shallower.size());
        assertEquals(2, deeper.size());
        assertEquals(shallower, deeper.subList(0, 1),
                "the deeper break is written under the shallower one's nesting and one more");
        assertNotSame(deeper.get(0), deeper.get(1),
                "and that one more is a nesting of its own — two nestings written the same way are"
                        + " two, so the levels are named rather than told apart by their amounts");
    }
}
