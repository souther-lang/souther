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
 * A walk from a seed whose step keeps the greater or the lesser of the answer so far and a value of
 * the element ends with that end of the seed and every element's value, so a comparison of what it
 * ends with is a comparison of the seed and of every element, or of some element.
 *
 * <p>{@code List.fold((w, l) -> if l.discount > w then l.discount else w, 0, lines) <= 10} holds
 * exactly where nought is at or below ten and every discount is, which is what
 * {@code List.all(l -> l.discount <= 10, lines)} states; at or above ten, it is the seed or some
 * discount, which is {@code List.any}. What is held here is that the comparison draws the lines and
 * is written the rows those forms are, however the step is spelled, that the least is the other way
 * round, that a seed settling the comparison leaves nothing to draw, and that a step keeping no end
 * of the two is not read as one.
 */
class AFoldThatKeepsAnEndIsReadAsEveryOrSomeElementTest {

    private static final String GREATER = "if l.discount > w then l.discount else w";

    private static final String LESSER = "if l.discount < w then l.discount else w";

    private static String model(String decided) {
        return """
                module example.worst

                data Line = { discount: Int }

                data Within
                data Needs

                behavior approval : (base: Int, lines: List<Line>) -> Within | Needs

                let approval (base, lines) =
                    if %s then Within else Needs
                """.formatted(decided);
    }

    private static String folded(String step, Object seed, String compared) {
        return model("List.fold((w, l) -> %s, %s, lines) %s".formatted(step, seed, compared));
    }

    /** At or below a number, the greatest is every element there, and the seed. */
    @Test
    void theGreatestAtOrBelowANumberIsEveryElementThere() {
        assertReadAs(model("List.all(l -> l.discount <= 10, lines)"),
                folded(GREATER, 0, "<= 10"));
        assertReadAs(model("List.all(l -> l.discount < 10, lines)"),
                folded(GREATER, 0, "< 10"));
    }

    /** At or above a number, the greatest is some element there, or the seed. */
    @Test
    void theGreatestAtOrAboveANumberIsSomeElementThere() {
        assertReadAs(model("List.any(l -> l.discount >= 10, lines)"),
                folded(GREATER, 0, ">= 10"));
        assertReadAs(model("List.any(l -> l.discount > 10, lines)"),
                folded(GREATER, 0, "> 10"));
    }

    /** The least is the other way round: some element below a number, and every one above it. */
    @Test
    void theLeastIsTheOtherWayRound() {
        assertReadAs(model("List.any(l -> l.discount < 10, lines)"),
                folded(LESSER, 100, "< 10"));
        assertReadAs(model("List.all(l -> l.discount >= 10, lines)"),
                folded(LESSER, 100, ">= 10"));
    }

    /** The step keeps the greater whichever way round it compares, and as a call of the library's
     *  own maximum, and the walk ends with the same number. */
    @Test
    void theStepKeepsTheSameEndHoweverItIsWritten() {
        Drawn plain = drawn(folded(GREATER, 0, "<= 10"));
        for (String step : List.of(
                "if w < l.discount then l.discount else w",
                "if l.discount <= w then w else l.discount",
                "if l.discount >= w then l.discount else w",
                "Int.max(w, l.discount)",
                "Int.max(l.discount, w)",
                "{ let d = l.discount  if d > w then d else w }",
                "{ let next = if l.discount > w then l.discount else w  next }",
                "{ let d = l.discount  let next = if d > w then d else w  next }")) {
            assertReadAs(plain, folded(step, 0, "<= 10"));
        }
    }

    /** The comparison was read, and what each element meets is a line on its discount; nothing of
     *  it is a total. */
    @Test
    void theComparisonDrawsTheLineOnTheElement() {
        String report = report(folded(GREATER, 0, "<= 10"));
        assertTrue(report.contains("read as approval/lines[*].discount: = 10"), report);
        assertTrue(report.contains("read as approval/lines[*].discount: = 11"), report);
        assertFalse(report.contains(MADE_FROM_IT), report);
        assertFalse(report.contains("List.sum"), report);
    }

    /** An equality is the end at or below and at or above, which is every element at or below and
     *  some at or above; a difference is some element above or every one below. */
    @Test
    void anEqualityAndADifferenceAreEveryAndSomeElementTogether() {
        assertReadAs(model("List.all(l -> l.discount <= 10, lines)"
                        + " && List.any(l -> l.discount >= 10, lines)"),
                folded(GREATER, 0, "== 10"));
        assertReadAs(model("List.any(l -> l.discount > 10, lines)"
                        + " || List.all(l -> l.discount < 10, lines)"),
                folded(GREATER, 0, "/= 10"));
    }

    /**
     * A seed the input holds is one more value the end is taken of, read beside every element or
     * some element as the comparison of it: the same lines, each owed the same points.
     *
     * <p>The rows are not the same, and are not meant to be. One comparison drawing two lines is
     * owed each point once, met on either line, as {@code Int.max(a, b) <= g} is; two comparisons
     * drawing one line each are owed each point twice.
     */
    @Test
    void aSeedTheInputHoldsIsComparedBesideTheElements() {
        assertDrawsThePointsOf(model("base <= 10 && List.all(l -> l.discount <= 10, lines)"),
                folded(GREATER, "base", "<= 10"));
        assertDrawsThePointsOf(model("base >= 10 || List.any(l -> l.discount >= 10, lines)"),
                folded(GREATER, "base", ">= 10"));
    }

    /**
     * A seed beyond the number settles the comparison whatever the elements are: the greatest of
     * eleven and anything is never at or below ten, and always at or above it. Read to the end, it
     * cuts nothing.
     */
    @Test
    void aSeedThatSettlesTheComparisonLeavesNothingToDraw() {
        for (String compared : List.of("<= 10", ">= 10")) {
            String report = report(folded(GREATER, 11, compared));
            assertTrue(report.contains("it was read to the end and cuts nothing"),
                    () -> compared + ": " + report);
            assertFalse(report.contains("ON point"), () -> compared + ": " + report);
            assertFalse(report.contains(MADE_FROM_IT), () -> compared + ": " + report);
        }
    }

    /**
     * What the step compares inside it is the element against the greatest of the seed and the
     * elements before it, which no value of the element settles on its own above the seed. That is
     * still said of it: reading the walk's end says nothing of that comparison.
     */
    @Test
    void theComparisonInsideTheStepIsStillSaidToRelateTwoValues() {
        String report = report(folded(GREATER, 0, "<= 10"));
        assertTrue(report.contains("relates the value here to another value not shown to reach"
                + " every value here"), report);
    }

    /**
     * A step that adds to what it chose, chooses by something other than how the two stand,
     * answers a value other than either, or keeps the greater over some elements and not others,
     * keeps no end of the two, and the comparison of what the walk ends with is not read.
     */
    @Test
    void aStepThatKeepsNoEndIsNotReadAsOne() {
        for (String step : List.of(
                "if l.discount > w then l.discount else w + 1",
                "if l.discount > 5 then l.discount else w",
                "if l.discount > w then l.discount else 0",
                "if l.discount > w then w else l.discount + 1",
                "Int.max(w, l.discount) + 1",
                "{ let d = w + 1  if l.discount > d then l.discount else d }")) {
            String report = report(folded(step, 0, "<= 10"));
            assertTrue(report.contains(MADE_FROM_IT), () -> step + ": " + report);
        }
    }

    /** What the walk walks has to be the list itself: over what a filter kept, every element is
     *  not every element of the list. */
    @Test
    void aWalkOverWhatAFilterKeptIsNotReadAsEveryElementOfTheList() {
        String report = report(model("List.fold((w, l) -> %s, 0, List.filter(l -> l.discount > 3,"
                .formatted(GREATER) + " lines)) <= 10"));
        assertTrue(report.contains(MADE_FROM_IT), report);
    }

    /**
     * A quote's worst discount: a rate wearing a name, compared through its value by the library's
     * order of decimals, the walk in a helper and the tier against it in the caller.
     */
    @Test
    void theWorstDiscountOfAQuoteIsRead() {
        String report = report("""
                module example.quoting

                data DiscountRate = Decimal
                data Line = { discount: DiscountRate }

                data Within
                data Needs

                behavior approval : (lines: List<Line>) -> Within | Needs

                let worstOf (lines: List<Line>): DiscountRate =
                    List.fold((worst, l) ->
                                  if Decimal.compare(l.discount.value, worst.value) > 0
                                  then l.discount else worst,
                              DiscountRate(0.0m), lines)

                let approval (lines) = {
                    let worst = worstOf(lines)
                    if Decimal.compare(worst.value, 0.10m) <= 0 then Within else Needs
                }
                """);
        assertTrue(report.contains("read as approval/lines[*].discount: = 0.1"), report);
        assertFalse(report.contains(MADE_FROM_IT), report);
    }

    /** Inside a conjunction, the comparison of the end is read as it is alone. */
    @Test
    void theEndComparedInsideAConjunctionIsReadAsItIsAlone() {
        assertReadAs(model("List.all(l -> l.discount <= 10, lines) && base > 3"),
                model("List.fold((w, l) -> %s, 0, lines) <= 10 && base > 3".formatted(GREATER)));
    }

    /**
     * A comparison stating that no element meets a relation draws the relation's line, whatever it
     * is a comparison of: here a truth that some element meets it, compared with false.
     */
    @Test
    void noElementMeetingARelationDrawsItsLine() {
        Drawn none = drawn(model("List.any(l -> l.discount > 10, lines) == false"));
        assertTrue(none.points().contains("ON approval/lines[*].discount: = 11"), none::report);
        assertTrue(none.points().contains("OFF approval/lines[*].discount: = 10"), none::report);
    }

    /** A step choosing by the sign of an order compared with a number written anywhere is
     *  choosing by the order of its arguments. */
    @Test
    void theSignOfAnOrderComparedWithANamedNumberChoosesByTheOrder() {
        String report = report("""
                module example.worst

                data Line = { d: Decimal }

                data Within
                data Needs

                behavior approval : (lines: List<Line>) -> Within | Needs

                let zero = 0

                let approval (lines) =
                    if List.fold((w, l) -> if Decimal.compare(l.d, w) > zero then l.d else w,
                                 0.0m, lines) <= 0.5m
                    then Within else Needs
                """);
        assertTrue(report.contains("read as approval/lines[*].d: = 0.5"), report);
        assertFalse(report.contains(MADE_FROM_IT), report);
    }

    /** A value wearing two names is compared through both, and is still the value. */
    @Test
    void aValueWearingTwoNamesIsComparedThroughBoth() {
        String report = report("""
                module example.worst

                data Inner = Int
                data Code = Inner
                data Line = { c: Code }

                data Within
                data Needs

                behavior approval : (lines: List<Line>) -> Within | Needs

                let approval (lines) =
                    if List.fold((w, l) -> if l.c.value.value > w.value.value then l.c else w,
                                 Code(Inner(0)), lines).value.value <= 3
                    then Within else Needs
                """);
        assertTrue(report.contains("read as approval/lines[*].c: = 3"), report);
        assertFalse(report.contains(MADE_FROM_IT), report);
    }

    /** What the report says of a comparison of a value made from a position and not worked out. */
    private static final String MADE_FROM_IT =
            "it is about a value made from this one, and what it says about the values here is not"
                    + " worked out";

    /** {@code read} draws the points {@code expected} draws, at the same values, and is written
     *  the same rows. */
    private static void assertReadAs(String expected, String read) {
        assertReadAs(drawn(expected), read);
    }

    private static void assertReadAs(Drawn expected, String read) {
        Drawn drawn = assertDrawsThePointsOf(expected, read);
        assertEquals(expected.rows(), drawn.rows(), () -> read + "\n" + drawn.report());
    }

    /** {@code read} draws the points {@code expected} draws, at the same values. */
    private static void assertDrawsThePointsOf(String expected, String read) {
        assertDrawsThePointsOf(drawn(expected), read);
    }

    private static Drawn assertDrawsThePointsOf(Drawn expected, String read) {
        assertFalse(expected.points().isEmpty(), () -> "the form it is held to draws points: "
                + expected.report());
        Drawn drawn = drawn(read);
        assertEquals(expected.points(), drawn.points(), () -> read + "\n" + drawn.report());
        assertFalse(drawn.rows().isEmpty(), () -> read + "\n" + drawn.report());
        return drawn;
    }

    /**
     * What one compilation of a model reports, the points it owes rows at and the rows written for
     * what nothing covers.
     */
    private record Drawn(String report, List<String> points, List<String> rows) {}

    private static Drawn drawn(String model) {
        Compilation compilation = compiled(model);
        String report = reportOf(compilation);
        return new Drawn(report, pointsOf(report), rowsOf(compilation));
    }

    /**
     * Each point the report says a row is owed at, once for each place it is read as, in order: a
     * comparison drawing two lines owes each point on both, as two comparisons drawing one each do.
     */
    private static List<String> pointsOf(String report) {
        Pattern point = Pattern.compile("row is at the (ON|OFF|IN|OUT) point \\(");
        Pattern readAs = Pattern.compile("^\\s+· read as (.+)$");
        List<String> out = new ArrayList<>();
        String owed = null;
        for (String line : report.split("\n")) {
            Matcher header = point.matcher(line);
            Matcher place = readAs.matcher(line);
            if (header.find()) {
                owed = header.group(1);
            } else if (owed != null && place.matches()) {
                out.add(owed + " " + place.group(1));
            } else {
                owed = null;
            }
        }
        out.sort(null);
        return out;
    }

    /**
     * Each row written for what nothing covers, whole however many lines its value takes, in
     * order. What a row is said to fill is left out: it names where the comparison is written.
     */
    private static List<String> rowsOf(Compilation compilation) {
        String rows = GeneratedRows.of(compilation, null, null,
                SourceRendering.namedByIdentity(SourceLayouts.NONE)).text();
        List<String> out = new ArrayList<>();
        StringBuilder row = null;
        for (String line : rows.split("\n")) {
            if (line.startsWith("    | ")) {
                if (row != null) {
                    out.add(row.toString().replaceAll("\\s+", " ").trim());
                }
                row = new StringBuilder(line);
            } else if (row != null && !line.startsWith("//") && !line.isBlank()) {
                row.append(' ').append(line);
            }
        }
        if (row != null) {
            out.add(row.toString().replaceAll("\\s+", " ").trim());
        }
        out.sort(null);
        return out;
    }

    private static String report(String model) {
        return reportOf(compiled(model));
    }

    private static String reportOf(Compilation compilation) {
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
