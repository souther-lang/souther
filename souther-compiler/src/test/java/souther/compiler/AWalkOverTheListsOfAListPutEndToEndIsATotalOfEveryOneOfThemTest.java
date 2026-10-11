package souther.compiler;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A walk over the lists of an outer list put end to end is a walk over every value standing at the
 * position inside them, so a total of it is a total of everything there and a rule about the total
 * is read, drawn lines on, and has rows written for it.
 *
 * <p>{@code List.fold(add, 0.0m, List.flatMap(.postings, entries))} was reported as about a value
 * made from the list and not worked out, though the same total over one list was read. What is held
 * here is that the number is the same whichever way the lists are put end to end and totalled, that
 * the rows written come to what their points ask whatever the lists are made to hold, and that a
 * walk over some of the values — the lists of one element, or what a filter kept — is not read as a
 * total of all of them.
 */
class AWalkOverTheListsOfAListPutEndToEndIsATotalOfEveryOneOfThemTest {

    private static final String DATA = """
            module example.nested

            data Many
            data Few

            data Posting = { q: Int }
            """;

    private static String model(String entryInvariant, String ledgerInvariant, String body) {
        return DATA + """

                data Entry = { postings: List<Posting> }
                %s

                data Ledger = { entries: List<Entry> }
                %s

                behavior decide : (ledger: Ledger) -> Many | Few

                let decide (ledger) =
                    if %s
                    then Many else Few
                """.formatted(entryInvariant, ledgerInvariant, body);
    }

    private static String total(String body) {
        return model("", "", body);
    }

    private static final String SUMMED =
            "List.sum(List.map(p -> p.q, List.flatMap(.postings, ledger.entries))) >= %d";

    private static final String FOLDED =
            "List.fold((acc, p) -> acc + p.q, 0, List.flatMap(.postings, ledger.entries)) >= %d";

    /** The same total however the lists are put end to end and added up. */
    @Test
    void aTotalOfTheListsPutEndToEndIsOneNumberHoweverItIsWritten() {
        for (String body : List.of(SUMMED, FOLDED)) {
            String report = report(total(body.formatted(4)));
            assertTrue(report.contains("List.sum(ledger.entries[*].postings[*].q)"),
                    () -> body + ": " + report);
            assertFalse(report.contains("not read"), () -> body + ": " + report);
        }
    }

    /** Every row is a row of the language, and comes to the total its point asks for. */
    @Test
    void theRowsWrittenComeToTheTotalsThePointsAskFor() {
        for (String body : List.of(SUMMED, FOLDED)) {
            List<Long> totals = totalsOf(rowsOf(total(body.formatted(4))));
            assertTrue(totals.contains(4L), () -> body + ": the point on the line: " + totals);
            assertTrue(totals.contains(3L), () -> body + ": the point just off it: " + totals);
            assertTrue(totals.stream().anyMatch(each -> each > 4), () -> body + ": " + totals);
            assertTrue(totals.stream().anyMatch(each -> each < 3), () -> body + ": " + totals);
        }
    }

    /**
     * A list that has to hold several elements, in a list that has to, is written with that many —
     * and a point no row was written for is said to be one the search left untried, never a point a
     * row reaches by holding fewer.
     */
    @Test
    void whatEachListHasToHoldIsHeldByTheRowsWritten() {
        String model = model("invariant List.length(postings) >= 2",
                "invariant List.length(entries) >= 2", SUMMED.formatted(10));
        String rows = rowsOf(model);
        List<Long> totals = totalsOf(rows);
        for (long point : List.of(10L, 9L)) {
            assertTrue(totals.contains(point) || rows.contains("no row for `List.sum("
                            + "ledger.entries[*].postings[*].q) = " + point + "`"),
                    () -> "the point " + point + " has a row or is said to have none: " + rows);
        }
        for (String row : rows.split("\n    \\| ")) {
            if (!row.contains("Entry")) {
                continue;
            }
            assertTrue(count(row, "Entry \\{") >= 2, () -> "two entries: " + row);
            assertTrue(count(row, "Posting \\{") >= 2 * count(row, "Entry \\{"),
                    () -> "two postings in each: " + row);
        }
    }

    /** What a filter kept, or a closure that chose among the lists, is not every value there. */
    @Test
    void aWalkOverSomeOfTheValuesIsNotATotalOfAllOfThem() {
        for (String body : List.of(
                "List.sum(List.map(p -> p.q, List.flatMap(.postings, "
                        + "List.filter(e -> List.length(e.postings) > 1, ledger.entries)))) >= %d",
                "List.sum(List.map(p -> p.q, List.flatMap(e -> List.filter(p -> p.q > 0, "
                        + "e.postings), ledger.entries))) >= %d",
                "List.fold((acc, p) -> acc + p.q, 0, List.flatMap(e -> List.take(1, e.postings), "
                        + "ledger.entries)) >= %d")) {
            String report = report(total(body.formatted(4)));
            assertFalse(report.contains("List.sum(ledger.entries[*].postings[*].q)"),
                    () -> body + ": " + report);
        }
    }

    /** A total over one element's list is a rule about each element, and no total of the lot. */
    @Test
    void aTotalInsideAnElementIsNotATotalOfEveryList() {
        String report = report(total("List.length(List.filter(e -> "
                + "List.sum(List.map(p -> p.q, e.postings)) >= 4, ledger.entries)) >= 1"));
        assertFalse(report.contains("List.sum(ledger.entries[*].postings[*].q)"), report);
    }

    /** A list with nothing in it adds nothing, and is a list a row may write. */
    @Test
    void listsThatHoldNothingAddNothing() {
        String rows = rowsOf(total("List.fold((acc, p) -> acc + p.q, 0, "
                + "List.flatMap(.postings, ledger.entries)) > 0"));
        List<Long> totals = totalsOf(rows);
        assertTrue(totals.contains(0L) || rows.contains("entries = []")
                        || rows.contains("postings = []"),
                () -> "a total of nothing is a total of nought: " + rows);
        assertTrue(totals.contains(1L), () -> "the point just over nought: " + rows);
    }

    /**
     * What a row written by hand comes to is every posting of every entry, whatever the lists hold:
     * lists of different lengths, a list with nothing in it, and no lists at all.
     */
    @Test
    void rowsWrittenByHandComeToEveryPostingOfEveryEntry() {
        String report = report(total(SUMMED.formatted(4)) + """

                example decide
                    | "on the line, over lists of unequal length" :
                        (Ledger { entries = [
                            Entry { postings = [Posting { q = 1 }, Posting { q = 2 }] },
                            Entry { postings = [] },
                            Entry { postings = [Posting { q = 1 }] }] }) -> Many
                    | "just off it" :
                        (Ledger { entries = [
                            Entry { postings = [Posting { q = 1 }, Posting { q = 2 }] },
                            Entry { postings = [] }] }) -> Few
                    | "nothing to total" : (Ledger { entries = [] }) -> Few
                """);
        assertTrue(report.contains("obligations 3/4"), report);
        assertTrue(report.contains("no row is at an IN point"), report);
        assertFalse(report.contains("no row is at an ON point"), report);
        assertFalse(report.contains("no row is at an OFF point"), report);
        assertFalse(report.contains("no row is at an OUT point"), report);
    }

    /** A comparison of a total of decimals with nought, over the lists of a list. */
    @Test
    void aTotalOfDecimalsComparedWithNoughtIsReadAndHasRows() {
        String model = """
                module p
                data Posting = { amount: Decimal }
                data Entry = { postings: List<Posting> }
                behavior f : (entries: List<Entry>) -> Bool
                let f (entries) = Decimal.compare(List.fold((acc, p) -> Decimal.add(acc, p.amount), 0.0m, List.flatMap(.postings, entries)), 0.0m) > 0
                """;
        String report = report(model);
        assertTrue(report.contains("List.sum(entries[*].postings[*].amount)"), report);
        assertFalse(report.contains("not read"), report);
        assertFalse(report.contains("made from this one"), report);

        List<java.math.BigDecimal> totals = new ArrayList<>();
        Pattern amount = Pattern.compile("amount = (-?[0-9.]+)m");
        for (String row : rowsOf(model).split("\n    \\| ")) {
            Matcher found = amount.matcher(row);
            java.math.BigDecimal total = java.math.BigDecimal.ZERO;
            while (found.find()) {
                total = total.add(new java.math.BigDecimal(found.group(1)));
            }
            totals.add(total);
        }
        assertTrue(totals.stream().anyMatch(each -> each.signum() > 0),
                () -> "a row whose postings come to more than nought: " + totals);
        assertTrue(totals.stream().anyMatch(each -> each.signum() <= 0),
                () -> "a row whose postings come to no more: " + totals);
    }

    /** The lists of the lists of a list are put end to end the same way, a level at a time. */
    @Test
    void listsPutEndToEndMoreThanOnceAreATotalOfEveryOne() {
        String report = report("""
                module example.deep

                data Many
                data Few

                data C = { q: Int }
                data B = { cs: List<C> }
                data A = { bs: List<B> }

                behavior decide : (groups: List<A>) -> Many | Few

                let decide (groups) =
                    if List.sum(List.map(c -> c.q,
                            List.flatMap(.cs, List.flatMap(.bs, groups)))) >= 4
                    then Many else Few
                """);
        assertTrue(report.contains("List.sum(groups[*].bs[*].cs[*].q)"), report);
        assertFalse(report.contains("not read"), report);
    }

    /** What each row's postings come to, over every entry of every ledger it writes. */
    private static List<Long> totalsOf(String rows) {
        List<Long> totals = new ArrayList<>();
        Pattern posting = Pattern.compile("Posting \\{ q = (-?\\d+) \\}");
        // One chunk per row, which is written over as many lines as its value needs.
        for (String row : rows.split("\n    \\| ")) {
            if (!row.contains("Ledger")) {
                continue;
            }
            Matcher found = posting.matcher(row);
            long total = 0;
            while (found.find()) {
                total += Long.parseLong(found.group(1));
            }
            totals.add(total);
        }
        return totals;
    }

    private static int count(String text, String regex) {
        Matcher found = Pattern.compile(regex).matcher(text);
        int n = 0;
        while (found.find()) {
            n++;
        }
        return n;
    }

    private static String rowsOf(String model) {
        return GeneratedRows.of(compiled(model), null, null,
                SourceRendering.namedByIdentity(SourceLayouts.NONE)).text();
    }

    private static String report(String model) {
        Compilation compilation = compiled(model);
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static Compilation compiled(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code().toString()).toList(),
                () -> "the source compiles: " + model);
        return compilation;
    }
}
