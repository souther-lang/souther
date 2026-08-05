package souther.compiler.diag;

import souther.compiler.Compiler;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A report quotes the characters the author typed and underlines all of them.
 *
 * <p>What a name is and how it is spelled are two answers, and a report wants the second: it is
 * about a place in a file, and the reader is looking at that place. A decomposed spelling is wider
 * than the composed name it denotes, so a report measured in the name stops short of the last
 * character — the caret sits under the middle of a word — and quotes back something the reader
 * cannot find in their file.
 *
 * <p>The spellings are written as the code points they are. A composed and a decomposed kana are
 * one glyph, so a fixture that says which one it means only in its glyphs means whatever the last
 * thing to save the file decided it meant.
 */
class AReportUnderlinesWhatTheAuthorTypedTest {

    /** A hiragana ka followed by a combining voiced sound mark - two UTF-16 units. */
    private static final String NFD = of(0x304b, 0x3099);
    /** The same kana as one code point. */
    private static final String NFC = of(0x304c);

    private static String of(int... codePoints) {
        return new String(codePoints, 0, codePoints.length);
    }

    @Test
    void theTwoSpellingsAreOneNameOfTwoWidths() {
        assertEquals(2, NFD.length());
        assertEquals(1, NFC.length());
    }

    @Test
    void anUnknownNameIsQuotedAsItWasWrittenAndUnderlinedThatWide() {
        Diagnostic report = only("""
                module demo

                data Box = { v: %s }
                """.formatted(NFD));

        assertTrue(List.of(report.args()).contains(NFD),
                "a reader is told about the name they wrote: " + List.of(report.args()));
        assertEquals(NFD.length(), width(report),
                "the underline stops inside the name it is about");
    }

    /**
     * A qualified name is underlined over the whole of what was written, qualifier included — and
     * the qualifier is what shrinks when it composes, so counting in the name misplaces the end
     * twice over.
     */
    @Test
    void aQualifiedUnknownNameIsUnderlinedOverTheWholeSpelling() {
        String written = NFD + ".Missing";
        Diagnostic report = only("""
                module demo

                data Box = { v: %s }
                """.formatted(written));

        assertEquals(written.length(), width(report));
    }

    /**
     * A qualified name is read over meaningful tokens, so what a report underlines runs from the
     * qualifier to the end of the name however far apart the two are written.
     *
     * <p>The joined spelling says nothing about the distance. Measuring the underline in it stops it
     * short by whatever stands between the parts, which is the same defect as measuring it in the
     * canonical name and is not fixed by keeping the spelling.
     */
    @Test
    void aQualifiedNameIsUnderlinedFromItsQualifierToItsEndHoweverFarApartTheyAre() {
        Diagnostic report = only("""
                module demo

                data Box = { v: %s . Missing }
                """.formatted(NFD));

        Region region = report.region();
        assertEquals(region.start().line(), region.end().line());
        assertEquals((NFD + " . Missing").length(),
                region.end().column() - region.start().column(),
                "the underline stops short of the name it is about");
    }

    /** The one report compiling {@code source} produces. */
    private static Diagnostic only(String source) {
        CompileException thrown =
                assertThrows(CompileException.class, () -> Compiler.compile(source));
        List<Diagnostic> all = thrown.diagnostics();
        assertEquals(1, all.size(), "one mistake, one report: " + all);
        return all.get(0);
    }

    /** How many columns a report's primary region covers. */
    private static int width(Diagnostic report) {
        Region region = report.region();
        assertEquals(region.start().line(), region.end().line(), "a name is one line's worth");
        return region.end().column() - region.start().column();
    }
}
