package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.ConditionOccurrence;
import souther.compiler.partition.ConditionReportAnchor;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The decision section writes an entry for each key its gaps differ by, and a sentence leaves out
 * part of what two gaps differ in, so two entries can read alike. A pointer to them is one entry
 * for each, as the section has them, and not one for each way of saying it.
 */
class APointerKeepsApartTheEntriesTheDecisionSectionKeepsApartTest {

    private static final ConditionReportAnchor ANCHOR = new ConditionReportAnchor.WhereTheReadingMetIt(
            "demo", new ConditionOccurrence("f", ConditionOccurrence.Reading.DECIDING, 0));

    @Test
    void twoEntriesThatReadAlikeAreTwoEntries() {
        AdequacyReport.SaidAlike one = new AdequacyReport.SaidAlike(ANCHOR, "one aspect");
        AdequacyReport.SaidAlike other = new AdequacyReport.SaidAlike(ANCHOR, "another aspect");
        Map<AdequacyReport.SaidAlike, String> entries = new LinkedHashMap<>();
        entries.put(one, "a condition on what Int.abs answers (8:50)");
        entries.put(other, "a condition on what Int.abs answers (8:50)");

        assertEquals(List.of("a condition on what Int.abs answers (8:50)",
                        "a condition on what Int.abs answers (8:50)"),
                AdequacyReport.entriesOf(new LinkedHashSet<>(List.of(one, other)), entries));
    }

    @Test
    void anEntryIsToldOnceHoweverManyGapsAreKeyedByIt() {
        AdequacyReport.SaidAlike one = new AdequacyReport.SaidAlike(ANCHOR, "one aspect");
        AdequacyReport.SaidAlike other = new AdequacyReport.SaidAlike(ANCHOR, "another aspect");
        Map<AdequacyReport.SaidAlike, String> entries = Map.of(one, "first", other, "second");

        Set<AdequacyReport.SaidAlike> keys = new LinkedHashSet<>(List.of(other, one, other));
        assertEquals(List.of("second", "first"), AdequacyReport.entriesOf(keys, entries));
    }
}
