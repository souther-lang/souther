package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A total of what {@code List.take} or {@code List.drop} keeps of a list is read as a total of the
 * list's elements weighed one where the position passes the test the library keeps them by and
 * nought where it does not, in the order they were kept in.
 *
 * <p>Some of the elements, so no total of the list: which of them is fixed by where each stands,
 * and the rows here are ones a total of the whole list, or of the elements kept from the other
 * end, would put somewhere else. A row is read at the border only where the reading puts its
 * elements where the library keeps them.
 *
 * <p>And only where the order is shown. Kept of a list in an order nothing declares, kept by a
 * count that is not written out, or kept before a walk numbers what it is handed afresh, a total
 * is not read by where the elements stand.
 */
class ATotalOfTheElementsKeptByAnIndexIsReadByWhereEachStandsTest {

    private static final String FIRST_TWO =
            "List.sum({if the position < 2 then 1·the element itself + 0 else 0 | xs[*]})";

    private static String model(String total, String rows) {
        return """
                module p
                data Line = { q: Int }
                data Yes = { n: Int }
                data No = { n: Int }
                behavior verify : (xs: List<Int>, ls: List<Line>, k: Int) -> Yes | No
                    constructs Yes, No
                let verify (xs, ls, k) =
                    if %s >= 5 then Yes { n = 0 } else No { n = 0 }
                %s
                """.formatted(total, rows);
    }

    /** The rows of the border at five, one for each of its points, the elements given. */
    private static String rows(String at, String below, String past, String shortOf) {
        return """
                example verify
                    | "at"    : (%s, [], 0) -> Yes { n = 0 }
                    | "below" : (%s, [], 0) -> No { n = 0 }
                    | "past"  : (%s, [], 0) -> Yes { n = 0 }
                    | "short" : (%s, [], 0) -> No { n = 0 }
                """.formatted(at, below, past, shortOf);
    }

    /**
     * The first two of {@code [2, 3, 100]} come to five, and the whole list to a hundred and five:
     * every point of the border is taken only on the reading of the elements before the count.
     */
    @Test
    void aTotalOfTheElementsBeforeTheCountIsReadOfThose() {
        String human = report(model("List.sum(List.take(2, xs))",
                rows("[2, 3, 100]", "[2, 2, 100]", "[3, 3, 0]", "[1, 2, 9]")));
        assertTrue(human.contains(FIRST_TWO), human);
        assertTrue(human.contains("obligations 4/4"), human);
        assertFalse(human.contains("not read:"), human);
    }

    /** From the count on, the elements before it count nought. */
    @Test
    void aTotalOfTheElementsFromTheCountOnIsReadOfThose() {
        String human = report(model("List.sum(List.drop(1, xs))",
                rows("[100, 2, 3]", "[100, 2, 2]", "[0, 3, 3]", "[9, 1, 2]")));
        assertTrue(human.contains(
                "List.sum({if the position >= 1 then 1·the element itself + 0 else 0 | xs[*]})"),
                human);
        assertTrue(human.contains("obligations 4/4"), human);
        assertFalse(human.contains("not read:"), human);
    }

    /**
     * Kept of the reverse, the first two are the last two the row writes: the same rows read from
     * the near end come to a hundred and two, and none of them is at five.
     */
    @Test
    void theElementsKeptOfTheReverseAreCountedFromTheFarEnd() {
        String human = report(model("List.sum(List.take(2, List.reverse(xs)))",
                rows("[100, 2, 3]", "[100, 2, 2]", "[0, 3, 3]", "[9, 1, 2]")));
        assertTrue(human.contains(FIRST_TWO.replace("xs[*]", "xs[*] from the far end")), human);
        assertTrue(human.contains("obligations 4/4"), human);
        assertFalse(human.contains("not read:"), human);
    }

    /**
     * What turns the kept elements round afterwards leaves their total as it was, and a name bound
     * to what was kept is what was kept: the same term as the elements before the count.
     */
    @Test
    void aReverseAfterTheKeepingAndANameForItAreTheSameTotal() {
        assertTrue(report(model("List.sum(List.reverse(List.take(2, xs)))", ""))
                .contains(FIRST_TWO));
        String named = report("""
                module p
                data Yes = { n: Int }
                data No = { n: Int }
                behavior verify : (xs: List<Int>) -> Yes | No
                    constructs Yes, No
                let verify (xs) = {
                    let ys = List.take(2, xs)
                    if List.sum(ys) >= 5 then Yes { n = 0 } else No { n = 0 }
                }
                """);
        assertTrue(named.contains(FIRST_TWO), named);
        assertFalse(named.contains("not read:"), named);
    }

    /**
     * Kept of what a map answered, the answers stand where their elements were handed, so the
     * total is of what the closure made of the first two: arithmetic of the element, or a field.
     */
    @Test
    void theElementsKeptOfWhatAMapAnsweredAreThoseItWasHanded() {
        Map<String, String> read = readEach(List.of(
                "List.sum(List.take(2, List.map(x -> 2 * x, xs)))",
                "List.sum(List.take(2, List.map(l -> l.q, ls)))"));
        String doubled = read.get("List.sum(List.take(2, List.map(x -> 2 * x, xs)))");
        assertTrue(doubled.contains(
                "List.sum({if the position < 2 then 2·the element itself + 0 else 0 | xs[*]})"),
                doubled);
        String field = read.get("List.sum(List.take(2, List.map(l -> l.q, ls)))");
        assertTrue(field.contains("List.sum({if the position < 2 then 1·q + 0 else 0 | ls[*]})"),
                field);
    }

    /**
     * Where the count reaches the length the elements kept are every one of them or none, and the
     * rows at the border are read so: the first two of {@code [2, 3]} are the list, of {@code [4]}
     * the one element, and of nothing nought.
     */
    @Test
    void theFirstOfAListNoLongerThanTheCountAreTheList() {
        String human = report(model("List.sum(List.take(2, xs))",
                rows("[2, 3]", "[4]", "[3, 3, 100]", "[]")));
        assertTrue(human.contains("obligations 4/4"), human);
        assertFalse(human.contains("not read:"), human);
    }

    /** And from the count on, a list no longer than the count keeps nothing. */
    @Test
    void theElementsPastTheCountOfAListNoLongerThanItAreNone() {
        String human = report(model("List.sum(List.drop(2, xs))",
                rows("[100, 100, 5]", "[100, 100, 4]", "[0, 0, 6]", "[100, 100]")
                        + "    | \"none\"   : ([], [], 0) -> No { n = 0 }\n"
                        + "    | \"one\"    : ([100], [], 0) -> No { n = 0 }\n"));
        assertTrue(human.contains("obligations 4/4"), human);
        assertFalse(human.contains("does not hold"), human);
    }

    /**
     * A count of nought or less keeps every element or none whatever the length, which is no
     * choice by position: from it on is the total of the list, and before it nought.
     */
    @Test
    void aCountOfNoughtOrLessKeepsTheWholeListOrNothing() {
        for (String whole : List.of("List.sum(List.drop(0, xs))", "List.sum(List.drop(-1, xs))")) {
            String human = report(model(whole, rows("[5]", "[4]", "[6]", "[3]")));
            assertTrue(human.contains("obligations 4/4"), whole + "\n" + human);
            assertFalse(human.contains("the position"), whole + "\n" + human);
        }
        // Every element kept is every element whatever their order, so a list nothing declares
        // the order of is kept whole as well.
        assertEquals(List.of(), notCancelling(List.of(
                "List.sum(List.drop(0, xs)) - List.sum(xs)",
                "List.sum(List.drop(-1, xs)) - List.sum(xs)",
                "List.sum(List.take(0, xs))",
                "List.sum(List.take(-1, xs))",
                "List.sum(List.drop(0, List.sort(xs))) - List.sum(xs)",
                "List.sum(List.drop(0, List.map(x -> 1 * x, List.sort(xs)))) - List.sum(xs)")));
    }

    /**
     * The total of the elements kept and the same total weighed by a choice of the position
     * written out are one number, so their difference is nought; and a total that turns on no
     * position, written as a walk, is the total of the list. The total of the first two less the
     * total of the list is no such nought, and is asked beside the others, so a reading that took
     * every difference for nought is told apart.
     */
    @Test
    void spellingsOfOneNumberAreOneTerm() {
        String notNought = "List.sum(List.take(2, xs)) - List.sum(xs)";
        assertEquals(List.of(notNought), notCancelling(List.of(
                "List.sum(List.take(2, xs))"
                        + " - List.sum(List.mapIndexed((i, x) -> if i < 2 then x else 0, xs))",
                "List.sum(List.take(2, List.reverse(xs)))"
                        + " - List.sum(List.mapIndexed((i, x) -> if i < 2 then x else 0,"
                        + " List.reverse(xs)))",
                "List.sum(xs) - List.sum(List.map(x -> 1 * x, xs))",
                "List.sum(xs) - List.fold((a, x) -> a + x, 0, xs)",
                "List.sum(List.map(x -> 3, xs)) - 3 * List.length(xs)",
                notNought)));
    }

    /** Which of {@code differences}, each compared against a number, is not read as nought — a
     *  comparison that cuts nothing — and is a line on a number of the input instead. */
    private static List<String> notCancelling(List<String> differences) {
        Map<String, String> read = readEach(differences);
        return differences.stream().filter(each -> {
            String human = read.get(each);
            return !human.contains("it was read to the end and cuts nothing")
                    || human.contains("draws its line") || human.contains("not read:");
        }).toList();
    }

    /**
     * What the report says of each of {@code totals}, compared against a number in a behavior of
     * its own: the behaviors are one module, measured once, and each total is read off its own
     * behavior's part of the report.
     */
    private static Map<String, String> readEach(List<String> totals) {
        StringBuilder module = new StringBuilder("""
                module p
                data Line = { q: Int }
                data Yes = { n: Int }
                data No = { n: Int }
                """);
        for (int at = 0; at < totals.size(); at++) {
            module.append("""
                    behavior verify%d : (xs: List<Int>, ls: List<Line>, k: Int) -> Yes | No
                        constructs Yes, No
                    let verify%d (xs, ls, k) =
                        if %s >= 5 then Yes { n = 0 } else No { n = 0 }
                    """.formatted(at, at, totals.get(at)));
        }
        String human = report(module.toString());
        Map<String, StringBuilder> parts = new LinkedHashMap<>();
        StringBuilder part = null;
        for (String line : human.lines().toList()) {
            Matcher behavior = BEHAVIOR.matcher(line);
            if (behavior.find()) {
                part = parts.computeIfAbsent(totals.get(Integer.parseInt(behavior.group(1))),
                        _ -> new StringBuilder());
            } else if (line.isBlank()) {
                part = null;
            }
            if (part != null) {
                part.append(line).append('\n');
            }
        }
        assertEquals(new LinkedHashSet<>(totals), parts.keySet(), human);
        Map<String, String> out = new LinkedHashMap<>();
        parts.forEach((total, said) -> out.put(total, said.toString()));
        return out;
    }

    /** The line a behavior's part of the report opens with. */
    private static final Pattern BEHAVIOR = Pattern.compile("^  verify(\\d+) ");

    /** Two counts keep two runs, and neither is the whole list. */
    @Test
    void twoCountsAreTwoTotalsAndNeitherIsTheWholeList() {
        String human = report(model(
                "List.sum(List.take(1, xs)) + List.sum(List.take(2, xs))", ""));
        assertTrue(human.contains(FIRST_TWO), human);
        assertTrue(human.contains(FIRST_TWO.replace("< 2", "< 1")), human);
        assertFalse(human.contains("List.sum(xs)"), human);
    }

    /**
     * Not read by where the elements stand: kept of a sorted list, whose order nothing declares;
     * by a count that is no number written out; before a walk, which numbers what it is handed from
     * nought again; or of a walk whose answers nothing puts in the order it was handed the elements.
     */
    @Test
    void aKeepingWhoseOrderIsNotShownIsNotRead() {
        readEach(List.of("List.sum(List.take(2, List.sort(xs)))",
                "List.sum(List.take(k, xs))",
                "List.sum(List.map(x -> 2 * x, List.take(2, xs)))",
                "List.sum(List.take(2, List.mapIndexed((i, x) -> i * x, xs)))"))
                .forEach((total, human) -> {
                    assertTrue(human.contains("not read: comparison"), total + "\n" + human);
                    assertFalse(human.contains("the position"), total + "\n" + human);
                });
    }

    private static String report(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }
}
