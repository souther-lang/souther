package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.util.List;
import java.util.Map;
import java.util.TreeMap;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An equality between two strings is parted by what the other can hold at the lengths some value
 * of the numbers the way ties the length to gets a run past, and at no other.
 *
 * <p>A way that holds the length of a string against a number the row writes — states a sum of
 * the two, or works one out that must stay within its type — is no reason to give the equality up:
 * for each length there may be a number that gets past, and the strings of a length none does for
 * are shown on neither side, whichever they would be on. A number the declarations tie to nothing
 * else is taken out of what the way says; one the way holds apart from a value is not.
 */
class AnOperationOnTheWayTyingAStringsLengthToANumberPartsTheStringsAtTheLengthsItGetsPastTest {

    private static final String ROWS = """
            module example.equal

            data L = String
                invariant String.matches("[a-z]+", value)

            data Row = { id: String, tag: String?, n: Int }

            let tagIs (text: String, r: Row): Bool =
                match r.tag with
                    | Some own -> %s && own == text
                    | None -> false

            behavior f : (a: L, rows: List<Row>) -> List<Row>

            let f (a, rows) = List.filter(r -> tagIs(a.value, r), rows)
            """;

    private static final String NUMBER = """
            module example.equal

            data L = String
                invariant String.matches("[a-z]+", value)

            data M = String
                invariant String.matches("[a-z0-9]+", value)

            data N = Int
                %s

            behavior f : (a: L, b: M, n: N) -> Bool

            let f (a, b, n) = {
                guard %s else false
                a.value == b.value
            }
            """;

    private static final String NOTHING_HELD = "";

    private static Compilation measured(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model under test compiles");
        return compilation;
    }

    private static PartitionEvidence evidenceOf(Compilation compilation) {
        PartitionEvidence evidence = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value().get("f");
        assertNotNull(evidence, "f is measured");
        return evidence;
    }

    /** The places of {@code f} whose equality is not shown to reach every value of them. */
    private static List<String> notShownToReachEveryValue(PartitionEvidence evidence) {
        return evidence.notRead().stream()
                .filter(each -> each.reason().name()
                        .equals("RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE"))
                .map(PartitionEvidence.NotRead::at).sorted().distinct().toList();
    }

    /** The same, of the two strings the equality is between. */
    private static List<String> stringsNotShownToReachEveryValue(PartitionEvidence evidence) {
        return notShownToReachEveryValue(evidence).stream()
                .filter(at -> at.equals("a") || at.equals("b")).toList();
    }

    /** The places whose classes stand over some of the values only. */
    private static List<String> shownOverARegion(PartitionEvidence evidence) {
        return evidence.notRead().stream()
                .filter(each -> each.reason().name().equals("RELATION_SHOWN_OVER_A_REGION"))
                .map(PartitionEvidence.NotRead::at).sorted().distinct().toList();
    }

    private static Map<String, List<String>> classesOf(PartitionEvidence evidence,
                                                       String... positions) {
        Map<String, List<String>> out = new TreeMap<>();
        evidence.axes().stream().filter(axis -> List.of(positions).contains(axis.path()))
                .forEach(axis -> out.put(axis.path(), axis.classes()));
        return out;
    }

    private static String json(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts()));
    }

    private static String human(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /** The statement of the issue: the sum of the string's length and a number of the row. */
    @Test
    void aSumOfALengthAndANumberOfTheRowLeavesBothStringsParted() {
        Compilation compilation = measured(ROWS.formatted("String.length(own) + r.n > 0"));

        assertEquals(List.of(), notShownToReachEveryValue(evidenceOf(compilation)));
        assertTrue(human(compilation).contains("measurement: complete"), human(compilation));
    }

    /**
     * The rows a number cannot carry past the addition are a stop of the run and no failure of
     * the relation: every run that gets to the comparison with a sum of the string's length and
     * the number past the greatest {@code Int} stops there.
     */
    @Test
    void theRowsANumberCannotCarryPastTheAdditionAreReportedAsAStop() {
        String report = human(measured(ROWS.formatted("String.length(own) + r.n > 0")));

        assertTrue(report.contains("every run stops in String.length(rows[*].tag@Some)"
                + " + rows[*].n where String.length(rows[*].tag@Some) + rows[*].n is at least"
                + " 9223372036854775808"), report);
    }

    private static final String MONTH = """
            module p
            data Month = { name: String, pay: Int }
            data Ok
            data No
            behavior f : (a: Month, b: Month) -> Ok | No
            let f (a, b) = {
                guard %s >= 300 else No
                Ok
            }
            """;

    /** A length is no more than the longest string, so two of them cannot pass the type. */
    @Test
    void aSumOfTwoLengthsIsNoStopSinceNoStringIsThatLong() {
        String report = human(measured(MONTH.formatted(
                "String.length(a.name) + String.length(b.name)")));

        assertFalse(report.contains("every run stops"), report);
    }

    /** And a length beside a number that may be the greatest {@code Int} can. */
    @Test
    void aSumOfALengthAndANumberThatMayBeTheGreatestIsAStop() {
        String report = human(measured(MONTH.formatted("String.length(a.name) + b.pay")));

        assertTrue(report.contains("every run stops in String.length(a.name) + b.pay where"
                + " String.length(a.name) + b.pay is at least 9223372036854775808"), report);
        assertFalse(report.contains("at most"), report);
    }

    /** The control: the operation reads no place the equality reads. */
    @Test
    void aNumberOfTheRowOnItsOwnLeavesBothStringsParted() {
        Compilation compilation = measured(ROWS.formatted("r.n + 1 > 0"));

        assertEquals(List.of(), notShownToReachEveryValue(evidenceOf(compilation)));
    }

    /** What the sum ties is read as the control reads what it does not: the same classes. */
    @Test
    void theClassesOfTheStringsAreTheOnesTheControlHas() {
        PartitionEvidence tied = evidenceOf(measured(
                NUMBER.formatted(NOTHING_HELD, "String.length(b.value) + n.value > 0")));
        PartitionEvidence control = evidenceOf(measured(
                NUMBER.formatted(NOTHING_HELD, "n.value > 0")));

        assertEquals(List.of("b/x can be a", "b/x is never a"),
                classesOf(tied, "b").get("b"));
        assertEquals(classesOf(control, "a", "b"), classesOf(tied, "a", "b"));
        assertEquals(List.of(), stringsNotShownToReachEveryValue(tied));
        assertEquals(List.of(), shownOverARegion(tied));
    }

    /**
     * The number is held to the three greatest {@code Int}s, so the sum stays within the type
     * only for a string of one or two code points: a longer string has no number that gets a run
     * past the addition. The strings it has are the classes, and the longer ones are open.
     */
    @Test
    void aNumberNearTheGreatestLeavesTheShortStringsPartedAndTheLongOnesOpen() {
        Compilation compilation = measured(NUMBER.formatted(
                "invariant value >= 9223372036854775805", "String.length(b.value) + n.value > 0"));
        PartitionEvidence evidence = evidenceOf(compilation);

        assertEquals(List.of(), stringsNotShownToReachEveryValue(evidence));
        assertEquals(List.of("b"), shownOverARegion(evidence));
        assertEquals(List.of("a/x can be b", "a/x is never b"), classesOf(evidence, "a").get("a"));
        assertEquals(List.of("b/x can be a", "b/x is never a"), classesOf(evidence, "b").get("b"));
        assertTrue(Pattern.compile("\"longerThan\"\\s*:\\s*2\\b").matcher(json(compilation)).find(),
                json(compilation));
    }

    private static final String ORIENTED = """
            module example.equal

            data A = String
                invariant String.matches("%s", value)

            data B = String
                invariant String.matches("%s", value)

            data N = Int
                invariant value >= 9223372036854775805

            behavior f : (a: A, b: B, n: N) -> Bool

            let f (a, b, n) = {
                %s
                a.value == b.value
            }
            """;

    private static final String LETTERS = "[a-z]+";

    private static final String LETTERS_AND_DIGITS = "[a-z0-9]+";

    /**
     * Whichever of the two strings holds the other's values, the string the way ties to a number
     * is parted at the lengths that get a run past, and its other lengths are open: the strings
     * the run stops on are not shown to be reached, nor are they shown on a side of the equality.
     * Held in either direction, and with the way stating the sum or only working it out.
     */
    @Test
    void theStringTheWayTiesIsOpenAtTheLengthsNoRunGetsPastWhicheverHoldsTheOther() {
        for (String ties : List.of("guard String.length(b.value) + n.value > 0 else false",
                "let total = String.length(b.value) + n.value")) {
            for (List<String> languages : List.of(List.of(LETTERS, LETTERS_AND_DIGITS),
                    List.of(LETTERS_AND_DIGITS, LETTERS))) {
                Compilation compilation = measured(
                        ORIENTED.formatted(languages.get(0), languages.get(1), ties));
                PartitionEvidence evidence = evidenceOf(compilation);
                String shape = ties + " over " + languages;

                assertEquals(List.of("b"), shownOverARegion(evidence), shape);
                assertEquals(List.of(), stringsNotShownToReachEveryValue(evidence), shape);
                assertTrue(Pattern.compile("\"longerThan\"\\s*:\\s*2\\b")
                        .matcher(json(compilation)).find(), shape);
            }
        }
    }

    /**
     * A sum the number cannot bring below nought is not one a string of any length gets a run
     * past: nothing arrives at the equality, which is said and not read as a rule owed.
     */
    @Test
    void aSumNoNumberCanBringBelowNoughtLeavesNothingArrivingAtTheEquality() {
        Compilation compilation = measured(NUMBER.formatted("invariant value >= 0",
                "String.length(b.value) + n.value < 0"));
        PartitionEvidence evidence = evidenceOf(compilation);

        assertEquals(List.of(), stringsNotShownToReachEveryValue(evidence));
        assertEquals(List.of(), shownOverARegion(evidence));
        assertTrue(human(compilation).contains("measurement: complete"), human(compilation));
    }

    /**
     * The number is held to at most five, so the sum is above ten only for a string of six code
     * points or more: a shorter string has no number that gets a run past the guard.
     */
    @Test
    void aNumberHeldFromAboveLeavesTheShortStringsOpen() {
        Compilation compilation = measured(NUMBER.formatted("invariant value <= 5",
                "String.length(b.value) + n.value > 10"));
        PartitionEvidence evidence = evidenceOf(compilation);

        assertEquals(List.of(), stringsNotShownToReachEveryValue(evidence));
        assertEquals(List.of("b"), shownOverARegion(evidence));
        assertTrue(Pattern.compile("\"shorterThan\"\\s*:\\s*6\\b").matcher(json(compilation)).find(),
                json(compilation));
    }

    /** The lengths that get past are all the lengths: nothing is left open. */
    @Test
    void aNumberAnywhereInItsTypeLeavesNoLengthOpen() {
        Compilation compilation = measured(NUMBER.formatted(NOTHING_HELD,
                "String.length(b.value) + n.value > 5"));

        assertEquals(List.of(), shownOverARegion(evidenceOf(compilation)));
        assertFalse(json(compilation).contains("leftOpen"), json(compilation));
    }

    /**
     * A number the way holds away from a value is held apart, not at a run of values: nothing is
     * said of the lengths it leaves, and the equality is not shown to be reached by every string.
     */
    @Test
    void aNumberTheWayHoldsAwayFromAValueIsNotTakenOut() {
        PartitionEvidence evidence = evidenceOf(measured(NUMBER.formatted(NOTHING_HELD,
                "String.length(b.value) + n.value > 0 && Bool.not(n.value == 5)")));

        assertEquals(List.of("a", "b"), stringsNotShownToReachEveryValue(evidence));
    }
}
