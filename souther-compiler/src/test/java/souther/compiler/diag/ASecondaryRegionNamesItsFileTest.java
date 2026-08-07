package souther.compiler.diag;


import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A diagnostic points at as many files as it has regions. What each region is quoted from, and what
 * a reader is told about where it is, is settled here rather than by whichever file the diagnostic
 * as a whole was filed under.
 */
class ASecondaryRegionNamesItsFileTest {

    private static final String ROW_FILE = """
            module m
            example f
              | "one" : (1) -> 2
            """;

    private static final String FAKE_FILE = """
            module n
            fake f
              | (1) -> 3
            """;

    private static SourceContext rows() {
        return new SourceContext("rows.sou", ROW_FILE);
    }

    private static SourceContext fakes() {
        return new SourceContext("fakes.sou", FAKE_FILE);
    }

    /** A resolver over named sources, recording what it was asked for. */
    private record Asked(List<String> ids, SourceContextResolver resolver) {}

    private static Asked resolver() {
        List<String> ids = new ArrayList<>();
        SourceContextResolver base = id -> {
            ids.add(id);
            if ("rows".equals(id)) {
                return rows();
            }
            return "fakes".equals(id) ? fakes() : null;
        };
        return new Asked(ids, SourceContextResolver.memoized(base::sourceOf));
    }

    private static Diagnostic withSecondary(String secondarySourceId) {
        return Diagnostic.uncoded("diag.hint.label")
                .at(new SourcePos(3, 3), 5)
                .secondaryIn(secondarySourceId, Region.ofWidth(new SourcePos(3, 3), 4),
                        "diag.hint.label")
                .build();
    }

    // --- what is quoted -------------------------------------------------------------------------

    @Test
    void aSecondaryInTheDiagnosticsOwnFileIsQuotedFromItAndNotNamed() {
        Asked asked = resolver();
        String out = new HumanRenderer(false).render(
                new Located(withSecondary(null), "rows"), asked.resolver(), Locale.ENGLISH);

        assertEquals(2, count(out, "  | \"one\" : (1) -> 2"),
                "the primary and the secondary both quote the row file: " + out);
        assertFalse(out.contains("fakes.sou"), out);
        assertEquals(1, count(out, "rows.sou"), "named once, in the title bar: " + out);
    }

    @Test
    void aSecondaryInAnotherFileIsQuotedFromThatFileAndNamed() {
        Asked asked = resolver();
        String out = new HumanRenderer(false).render(
                new Located(withSecondary("fakes"), "rows"), asked.resolver(), Locale.ENGLISH);

        assertTrue(out.contains("  | \"one\" : (1) -> 2"), "the primary quotes the row: " + out);
        assertTrue(out.contains("  | (1) -> 3"), "the secondary quotes the fake: " + out);
        assertTrue(out.contains("fakes.sou:3:3"), "and says where it is: " + out);
    }

    @Test
    void aDiagnosticThatNamesNoSourceIsQuotedFromWhateverTheCallerAnswersWith() {
        String out = new HumanRenderer(false).render(
                new Located(withSecondary(null), Located.NO_SOURCE),
                id -> rows(), Locale.ENGLISH);

        assertEquals(2, count(out, "  | \"one\" : (1) -> 2"), out);
        assertFalse(out.contains("null"), out);
    }

    @Test
    void aSourceIsReadOnceHoweverManyRegionsAreInIt() {
        Asked asked = resolver();
        Diagnostic d = Diagnostic.uncoded("diag.hint.label")
                .at(new SourcePos(3, 3), 5)
                .secondaryIn("fakes", Region.ofWidth(new SourcePos(3, 3), 4), "diag.hint.label")
                .secondaryIn("fakes", Region.ofWidth(new SourcePos(2, 1), 4), "diag.hint.label")
                .build();

        new HumanRenderer(false).render(new Located(d, "rows"), asked.resolver(), Locale.ENGLISH);

        assertEquals(1, count(asked.ids(), "fakes"),
                "two regions in one file, one read: " + asked.ids());
    }

    // --- JSON -----------------------------------------------------------------------------------

    @Test
    void jsonNamesNoFileForASecondaryInTheDiagnosticsOwnFile() {
        Asked asked = resolver();
        String out = new JsonRenderer().render(
                new Located(withSecondary(null), "rows"), asked.resolver(), Locale.ENGLISH);

        assertEquals(1, count(out, "\"file\""), "only the top-level file: " + out);
    }

    @Test
    void jsonNamesTheFileOfASecondaryWrittenInAnother() {
        Asked asked = resolver();
        String out = new JsonRenderer().render(
                new Located(withSecondary("fakes"), "rows"), asked.resolver(), Locale.ENGLISH);

        assertTrue(out.contains("\"file\":\"rows.sou\""), out);
        assertTrue(out.contains("\"file\":\"fakes.sou\""), out);
    }

    // --- which region a file reads the diagnostic at ---------------------------------------------

    @Test
    void theFileHoldingTheSecondaryReadsItAsTheAnchorAndThePrimaryAsElsewhere() {
        Diagnostic d = withSecondary("fakes");

        DiagnosticView own = DiagnosticView.of(d, "rows", "rows");
        assertEquals("rows", own.anchor().sourceId());
        assertFalse(own.anchor().labelled(), "the primary region carries no note of its own");
        assertEquals(List.of("fakes"), own.others().stream().map(Spot::sourceId).toList());

        DiagnosticView other = DiagnosticView.of(d, "rows", "fakes");
        assertEquals("fakes", other.anchor().sourceId(), "the two change places");
        assertTrue(other.anchor().labelled());
        assertEquals(List.of("rows"), other.others().stream().map(Spot::sourceId).toList());
    }

    @Test
    void aSecondaryThatNamesNoSourceInheritsTheDiagnosticsOwn() {
        DiagnosticView view = DiagnosticView.of(withSecondary(null), "rows", "rows");

        assertEquals(List.of("rows"), view.others().stream().map(Spot::sourceId).toList());
        assertNull(withSecondary(null).secondary().get(0).sourceId(),
                "the region itself still names none");
    }

    @Test
    void aFileNoRegionIsInIsRefusedRatherThanAnchoredSomewhereElse() {
        Diagnostic d = withSecondary("fakes");

        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> DiagnosticView.of(d, "rows", "elsewhere"));

        assertTrue(refused.getMessage().contains("elsewhere"), refused.getMessage());
    }

    @Test
    void whereOneFileHoldsSeveralRegionsTheFirstWrittenIsTheAnchor() {
        Diagnostic d = Diagnostic.uncoded("diag.hint.label")
                .at(new SourcePos(3, 3), 5)
                .secondaryIn("fakes", Region.ofWidth(new SourcePos(3, 3), 4), "diag.hint.label")
                .secondaryIn("fakes", Region.ofWidth(new SourcePos(2, 1), 4), "diag.hint.label")
                .build();

        DiagnosticView view = DiagnosticView.of(d, "rows", "fakes");

        assertEquals(3, view.anchor().region().start().line(),
                "declaration order, not the earlier line");
        assertEquals(2, view.others().size());
    }

    // --- a label and its region say one file, or one of them says nothing -----------------------

    /**
     * Two things here can say which file a secondary is in: what the label was given, and what its
     * region's own position was read from. A reader takes the first, so if they can disagree the
     * file a marker is put in and the file its line is quoted from come apart again — the shape of
     * mistake this whole change is about. They are refused at construction instead.
     */
    @Test
    void aLabelAndItsRegionCannotNameTwoFiles() {
        assertThrows(IllegalArgumentException.class,
                () -> new LabeledRegion(Region.ofWidth(new SourcePos(3, 3, "rows"), 4),
                        "fakes", "diag.hint.label", null));
    }

    /** A region built from a hand-made position knows no file, and a label that names one is how it
     *  is told — which is what every site that points across files does. */
    @Test
    void aLabelMayNameTheFileWhenItsRegionDoesNot() {
        assertEquals("fakes", new LabeledRegion(Region.ofWidth(new SourcePos(3, 3), 4),
                "fakes", "diag.hint.label", null).sourceId());
    }

    /** A label that names nothing means the diagnostic's own file, whatever its region was read
     *  from — that is what {@link LabeledRegion#sourceIdOr(String)} is for. */
    @Test
    void aLabelMayNameNothingWhileItsRegionKnowsItsFile() {
        LabeledRegion label = new LabeledRegion(Region.ofWidth(new SourcePos(3, 3, "rows"), 4),
                null, "diag.hint.label", null);

        assertEquals("rows", label.sourceIdOr("rows"));
    }

    private static int count(String text, String part) {
        int found = 0;
        for (int at = text.indexOf(part); at >= 0; at = text.indexOf(part, at + 1)) {
            found++;
        }
        return found;
    }

    private static int count(List<String> asked, String id) {
        return (int) asked.stream().filter(id::equals).count();
    }
}
