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

                behavior approval : (lines: List<Line>) -> Within | Needs

                let approval (lines) =
                    if %s then Within else Needs
                """.formatted(decided);
    }

    private static String folded(String step, int seed, String compared) {
        return model("List.fold((w, l) -> %s, %d, lines) %s".formatted(step, seed, compared));
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
        String plain = folded(GREATER, 0, "<= 10");
        for (String step : List.of(
                "if w < l.discount then l.discount else w",
                "if l.discount <= w then w else l.discount",
                "if l.discount >= w then l.discount else w",
                "Int.max(w, l.discount)",
                "Int.max(l.discount, w)")) {
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

    /** An equality is the end at or below and at or above, and a difference either side of it;
     *  both are read. */
    @Test
    void anEqualityAndADifferenceAreRead() {
        for (String compared : List.of("== 10", "/= 10")) {
            String report = report(folded(GREATER, 0, compared));
            assertTrue(report.contains("read as approval/lines[*].discount: = 10"),
                    () -> compared + ": " + report);
            assertFalse(report.contains(MADE_FROM_IT), () -> compared + ": " + report);
        }
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
                "Int.max(w, l.discount) + 1")) {
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
     * The model the fold was first missed in, as it was written: a rate wearing a name, compared
     * through its value by the library's order of decimals, the walk in a helper and the tiers
     * against it in the caller.
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

    /** What the report says of a comparison of a value made from a position and not worked out. */
    private static final String MADE_FROM_IT =
            "it is about a value made from this one, and what it says about the values here is not"
                    + " worked out";

    /** {@code read} draws the points {@code expected} draws, at the same values, and is written
     *  the same rows. */
    private static void assertReadAs(String expected, String read) {
        String expectedReport = report(expected);
        String readReport = report(read);
        List<String> points = pointsOf(expectedReport);
        assertFalse(points.isEmpty(), () -> "the form it is held to draws points: "
                + expectedReport);
        assertEquals(points, pointsOf(readReport), () -> read + "\n" + readReport);
        assertEquals(rowsOf(expected), rowsOf(read), () -> read + "\n" + readReport);
    }

    /** Each point the report says a row is owed at, and what it is read as, in order. */
    private static List<String> pointsOf(String report) {
        Pattern point = Pattern.compile(
                "row is at the (ON|OFF|IN|OUT) point \\([^)]*\\)[^\\n]*\\n\\s+· read as ([^\\n]+)");
        List<String> out = new ArrayList<>();
        Matcher found = point.matcher(report);
        while (found.find()) {
            out.add(found.group(1) + " " + found.group(2));
        }
        out.sort(null);
        return out;
    }

    /** The values of each row written for what nothing covers, in order. */
    private static List<String> rowsOf(String model) {
        String rows = GeneratedRows.of(compiled(model), null, null,
                SourceRendering.namedByIdentity(SourceLayouts.NONE)).text();
        List<String> out = new ArrayList<>();
        for (String line : rows.split("\n")) {
            if (line.startsWith("    | ")) {
                out.add(line.replaceAll("\\s+", " ").trim());
            }
        }
        out.sort(null);
        return out;
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
