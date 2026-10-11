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
     * A list that has to hold several elements, in a list that has to, is written with that many,
     * and the total is spread over the leaves of all of them.
     */
    @Test
    void whatEachListHasToHoldIsHeldByTheRowsWritten() {
        String model = model("invariant List.length(postings) >= 2",
                "invariant List.length(entries) >= 2", SUMMED.formatted(10));
        String rows = rowsOf(model);
        List<Long> totals = totalsOf(rows);
        assertTrue(totals.contains(10L), () -> "the point on the line: " + rows);
        assertTrue(totals.contains(9L), () -> "the point just off it: " + rows);
        assertTrue(totals.stream().anyMatch(each -> each > 10), () -> "one inside: " + rows);
        assertTrue(totals.stream().anyMatch(each -> each < 9), () -> "one outside: " + rows);
        for (String row : rows.split("\n    \\| ")) {
            if (!row.contains("Entry")) {
                continue;
            }
            assertTrue(count(row, "Entry \\{") >= 2, () -> "two entries: " + row);
            assertTrue(count(row, "Posting \\{") >= 2 * count(row, "Entry \\{"),
                    () -> "two postings in each: " + row);
        }
    }

    /**
     * What a leaf may be and how many of them a list may hold bound what the lists can come to, so
     * the total is spread over as many leaves as it takes and no list is written past its end.
     */
    @Test
    void aTotalPastWhatOneLeafHoldsIsSpreadOverMoreLeaves() {
        String model = DATA.replace("data Posting = { q: Int }", """
                data Posting = { q: Int }
                    invariant q >= 0 && q <= 3""") + """

                data Entry = { postings: List<Posting> }
                    invariant List.length(postings) >= 1 && List.length(postings) <= 2

                data Ledger = { entries: List<Entry> }
                    invariant List.length(entries) >= 1 && List.length(entries) <= 2

                behavior decide : (ledger: Ledger) -> Many | Few

                let decide (ledger) =
                    if %s
                    then Many else Few
                """.formatted(SUMMED.formatted(10));
        String rows = rowsOf(model);
        List<Long> totals = totalsOf(rows);
        assertTrue(totals.contains(10L), () -> "the point on the line: " + rows);
        assertTrue(totals.contains(9L), () -> "the point just off it: " + rows);
        for (String row : rows.split("\n    \\| ")) {
            if (!row.contains("Ledger")) {
                continue;
            }
            Matcher found = Pattern.compile("q = (-?\\d+)").matcher(row);
            while (found.find()) {
                long q = Long.parseLong(found.group(1));
                assertTrue(q >= 0 && q <= 3, () -> "a posting inside its own rule: " + row);
            }
            assertTrue(count(row, "Entry \\{") <= 2, () -> "at most two entries: " + row);
        }
        // Four postings of three at most come to twelve, so a total past that has no row.
        String past = rowsOf(model.replace(">= 10", ">= 13"));
        assertTrue(totalsOf(past).stream().noneMatch(each -> each == 13L), past);
    }

    /** Lists the rules leave any size are written at more than one, the postings of an entry
     *  differing in number from the postings of the next. */
    @Test
    void listsOfAnySizeAreWrittenAtMoreThanOneSize() {
        String rows = rowsOf(model("", "invariant List.length(entries) >= 2", SUMMED.formatted(10)));
        boolean unequal = false;
        for (String row : rows.split("\n    \\| ")) {
            List<Integer> sizes = new ArrayList<>();
            for (String entry : row.split("Entry \\{")) {
                if (entry.contains("postings")) {
                    sizes.add(count(entry, "Posting \\{"));
                }
            }
            unequal |= sizes.stream().distinct().count() > 1;
        }
        assertTrue(totalsOf(rows).contains(10L), rows);
        assertTrue(unequal, () -> "a row whose entries hold different numbers of postings: " + rows);
    }

    /**
     * Levels that only say how many they hold at least, and say nothing of the most, hold as many
     * as a count can be: the capacity of three such levels is past what a count of leaves is held
     * in, and a level asked for a few of them is still one that holds the leaves.
     */
    @Test
    void levelsWithNoCeilingStillHoldTheLeavesAskedOfThem() {
        String model = """
                module example.deep

                data Many
                data Few

                data C = { q: Int }
                data B = { cs: List<C> }
                    invariant List.length(cs) >= 2
                data A = { bs: List<B> }
                    invariant List.length(bs) >= 2
                data Groups = { groups: List<A> }
                    invariant List.length(groups) >= 3

                behavior decide : (all: Groups) -> Many | Few

                let decide (all) =
                    if List.sum(List.map(c -> c.q,
                            List.flatMap(.cs, List.flatMap(.bs, all.groups)))) >= 7
                    then Many else Few
                """;
        String rows = rowsOf(model);
        Pattern leaf = Pattern.compile("C \\{ q = (-?\\d+) \\}");
        boolean fewestGroupsAtThePoint = false;
        for (String row : rows.split("\n    \\| ")) {
            Matcher found = leaf.matcher(row);
            long total = 0;
            boolean any = false;
            while (found.find()) {
                total += Long.parseLong(found.group(1));
                any = true;
            }
            if (any) {
                assertTrue(count(row, "A \\{") >= 3, () -> "three groups: " + row);
                // The grouping written is the one of the fewest elements each level allows, which
                // is three groups of two lists of two leaves where each level's count has a floor
                // and no ceiling — what the other ways of writing a row are not asked to be.
                fewestGroupsAtThePoint |= total == 7L && count(row, "A \\{") == 3
                        && count(row, "C \\{") == 12;
            }
        }
        assertTrue(fewestGroupsAtThePoint, () -> "the point on the line, at the fewest: " + rows);
    }

    /** The same spreading through three levels of lists. */
    @Test
    void aTotalOverThreeLevelsOfListsIsSpreadOverTheLeavesOfAll() {
        String model = """
                module example.deep

                data Many
                data Few

                data C = { q: Int }
                data B = { cs: List<C> }
                    invariant List.length(cs) >= 2
                data A = { bs: List<B> }
                    invariant List.length(bs) >= 2

                behavior decide : (groups: List<A>) -> Many | Few

                let decide (groups) =
                    if List.sum(List.map(c -> c.q,
                            List.flatMap(.cs, List.flatMap(.bs, groups)))) >= 7
                    then Many else Few
                """;
        String rows = rowsOf(model);
        List<Long> totals = new ArrayList<>();
        Pattern leaf = Pattern.compile("C \\{ q = (-?\\d+) \\}");
        for (String row : rows.split("\n    \\| ")) {
            Matcher found = leaf.matcher(row);
            long total = 0;
            boolean any = false;
            while (found.find()) {
                total += Long.parseLong(found.group(1));
                any = true;
            }
            if (any) {
                totals.add(total);
                assertTrue(count(row, "B \\{") >= 2 * count(row, "A \\{"), row);
                assertTrue(count(row, "C \\{") >= 2 * count(row, "B \\{"), row);
            }
        }
        assertTrue(totals.contains(7L), () -> "the point on the line: " + rows);
        assertTrue(totals.contains(6L), () -> "the point just off it: " + rows);
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
