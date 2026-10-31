package souther.compiler;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.partition.UndividedPosition;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;
import souther.compiler.report.WhyAPlaceIsUndividedIsSaid;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
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
 *
 * <p>The comparison the step makes is read as well: the element against the end kept of the seed
 * and the elements before it. Where the seed is past every value a discount takes, it divides no
 * discount, so the walks below start there and what they draw is the comparison of the end alone.
 * Where it is not, it parts the discounts at the seed
 * ({@link #theComparisonInsideTheStepPartsTheDiscountsAtTheSeed}).
 */
class AFoldThatKeepsAnEndIsReadAsEveryOrSomeElementTest {

    private static final String GREATER = "if l.discount > w then l.discount else w";

    private static final String LESSER = "if l.discount < w then l.discount else w";

    /** Below every discount, so the greatest is kept from it with nothing the step parts. */
    private static final int BELOW = -1;

    /** Above every discount, the same for the least. */
    private static final int ABOVE = 101;

    private static String model(String decided) {
        return model("invariant discount >= 0 && discount <= 100", decided);
    }

    private static String model(String ofALine, String decided) {
        return """
                module example.worst

                data Line = { discount: Int }
                    %s

                data Within
                data Needs

                behavior approval : (base: Int, lines: List<Line>) -> Within | Needs

                let approval (base, lines) =
                    if %s then Within else Needs
                """.formatted(ofALine, decided);
    }

    private static String folded(String step, Object seed, String compared) {
        return model("List.fold((w, l) -> %s, %s, lines) %s".formatted(step, seed, compared));
    }

    /** At or below a number, the greatest is every element there, and the seed. */
    @Test
    void theGreatestAtOrBelowANumberIsEveryElementThere() {
        assertReadAs(model("List.all(l -> l.discount <= 10, lines)"),
                folded(GREATER, BELOW, "<= 10"));
        assertReadAs(model("List.all(l -> l.discount < 10, lines)"),
                folded(GREATER, BELOW, "< 10"));
    }

    /** At or above a number, the greatest is some element there, or the seed. */
    @Test
    void theGreatestAtOrAboveANumberIsSomeElementThere() {
        assertReadAs(model("List.any(l -> l.discount >= 10, lines)"),
                folded(GREATER, BELOW, ">= 10"));
        assertReadAs(model("List.any(l -> l.discount > 10, lines)"),
                folded(GREATER, BELOW, "> 10"));
    }

    /** The least is the other way round: some element below a number, and every one above it. */
    @Test
    void theLeastIsTheOtherWayRound() {
        assertReadAs(model("List.any(l -> l.discount < 10, lines)"),
                folded(LESSER, ABOVE, "< 10"));
        assertReadAs(model("List.all(l -> l.discount >= 10, lines)"),
                folded(LESSER, ABOVE, ">= 10"));
    }

    /**
     * The step keeps the greater whichever way round it compares, and as a call of the library's
     * own maximum, and the walk ends with the same number.
     *
     * <p>Over discounts with no greatest, since what the step's own comparison parts turns on how
     * it is written: kept by {@code l.discount >= w}, the greatest discount there is would pass
     * every end kept, and that comparison would part it from the rest.
     */
    @Test
    void theStepKeepsTheSameEndHoweverItIsWritten() {
        String unbounded = "invariant discount >= 0";
        Drawn plain = drawn(model(unbounded, "List.fold((w, l) -> %s, %d, lines) <= 10"
                .formatted(GREATER, BELOW)));
        for (String step : List.of(
                "if w < l.discount then l.discount else w",
                "if l.discount <= w then w else l.discount",
                "if l.discount >= w then l.discount else w",
                "Int.max(w, l.discount)",
                "Int.max(l.discount, w)",
                "{ let d = l.discount  if d > w then d else w }",
                "{ let d = l.discount  if l.discount > w then d else w }",
                "{ let next = if l.discount > w then l.discount else w  next }",
                "{ let d = l.discount  let next = if d > w then d else w  next }")) {
            assertReadAs(plain, model(unbounded, "List.fold((w, l) -> %s, %d, lines) <= 10"
                    .formatted(step, BELOW)));
        }
    }

    /** The comparison was read, and what each element meets is a line on its discount; nothing of
     *  it is a total. */
    @Test
    void theComparisonDrawsTheLineOnTheElement() {
        String report = report(folded(GREATER, BELOW, "<= 10"));
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
                folded(GREATER, BELOW, "== 10"));
        assertReadAs(model("List.any(l -> l.discount > 10, lines)"
                        + " || List.all(l -> l.discount < 10, lines)"),
                folded(GREATER, BELOW, "/= 10"));
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
            assertFalse(report.contains("row is at the ON point (comparison@"),
                    () -> compared + ": " + report);
            assertFalse(report.contains(MADE_FROM_IT), () -> compared + ": " + report);
        }
    }

    /**
     * What the step compares is the element against the end kept of the seed and the elements
     * before it, which lies between the seed and the furthest discount past it and takes every
     * value there. With the seed past every discount, each discount has that end on both sides of
     * it on some list, so the comparison divides no discount; and a rule of the element's own,
     * which is about one element, ties it to none of the others the end was kept of.
     */
    @Test
    void theComparisonInsideTheStepDividesNoDiscountWhereTheSeedIsPastThemAll() {
        for (String walk : List.of(folded(GREATER, BELOW, "<= 10"),
                folded(LESSER, ABOVE, ">= 10"))) {
            String report = report(walk);
            assertTrue(report.contains(RELATES_ANOTHER_VALUE), () -> walk + "\n" + report);
            assertFalse(report.contains(NOT_SHOWN_TO_REACH), () -> walk + "\n" + report);
        }
    }

    /**
     * Where the seed is a value a discount takes, a discount at or below it never passes what was
     * kept, which is the seed or more, and one above it may or may not: the comparison parts the
     * discounts at the seed, as a line of no comparison the author wrote. So does a seed below
     * every discount where nothing bounds them, and one where the list holds one element at most,
     * which the end is then the seed alone against.
     */
    @Test
    void theComparisonInsideTheStepPartsTheDiscountsAtTheSeed() {
        Drawn fromNought = drawn(folded(GREATER, 0, "<= 10"));
        assertFalse(fromNought.report().contains(NOT_SHOWN_TO_REACH), fromNought::report);
        assertTrue(fromNought.report().contains(
                "no IN point is owed at lines[*].discount = 0 (comparison@"),
                fromNought::report);
        Drawn unbounded = drawn(model("", "List.fold((w, l) -> %s, 0, lines) <= 10"
                .formatted(GREATER)));
        assertFalse(unbounded.report().contains(NOT_SHOWN_TO_REACH), unbounded::report);
        assertTrue(unbounded.written().stream()
                        .anyMatch(row -> row.isFor("lines[*].discount: x <= 0 at lines[*].discount")),
                () -> unbounded.report() + "\n" + unbounded.rows());
        String alone = report("""
                module example.worst

                data Line = { discount: Int }
                    invariant discount >= 0 && discount <= 100
                data Quote = { lines: List<Line> }
                    invariant List.length(lines) <= 1

                data Within
                data Needs

                behavior approval : (quote: Quote) -> Within | Needs

                let approval (quote) =
                    if List.fold((w, l) -> %s, 0, quote.lines) <= 10 then Within else Needs
                """.formatted(GREATER));
        assertFalse(alone.contains(NOT_SHOWN_TO_REACH), alone);
        assertTrue(alone.contains("no IN point is owed at quote.lines[*].discount = 0"), alone);
    }

    /** Over decimals the comparison in the step parts the discounts at the seed as well: nought is
     *  settled, and a discount above it is not. */
    @Test
    void theComparisonInsideTheStepPartsDecimalDiscountsAtTheSeed() {
        Drawn drawn = drawn("""
                module example.worst

                data Line = { discount: Decimal }
                    invariant discount >= 0.0m && discount <= 1.0m

                data Within
                data Needs

                behavior approval : (lines: List<Line>) -> Within | Needs

                let approval (lines) =
                    if List.fold((w, l) -> %s, 0.0m, lines) <= 0.1m then Within else Needs
                """.formatted(GREATER));
        assertFalse(drawn.report().contains(NOT_SHOWN_TO_REACH), drawn::report);
        assertTrue(drawn.report().contains(
                "no IN point is owed at lines[*].discount = 0 (comparison@"), drawn::report);
        assertTrue(drawn.report().contains(
                "read as approval/lines[*].discount: in 0 < lines[*].discount < 0.1"),
                drawn::report);
    }

    /**
     * What holds of the element the step is applied to holds of no element before it. A step
     * choosing only under a condition on its element keeps no end, so neither its comparison of
     * the end nor the comparison inside it is read as one; and under a condition on another
     * element of the same list, the end may still have been kept of a discount above it, so the
     * greatest discount there is is what passes every end, at a hundred and not at five.
     *
     * <p>The second holds today whatever the end kept is read over, since what that condition
     * states does not reach the region the comparison inside the step is read in. It is here for
     * the day it does: the end is kept of elements the condition says nothing of.
     */
    @Test
    void whatHoldsOfOneElementIsNotTakenOfTheOnesTheEndWasKeptOf() {
        String guarded = report(folded("if l.discount <= 5 then (if l.discount > w then"
                + " l.discount else w) else w", BELOW, "<= 10"));
        assertTrue(guarded.contains(ON_ITS_RUNS), guarded);
        assertTrue(guarded.contains(NOT_SHOWN_TO_REACH), guarded);
        String another = report(model("List.any(m -> m.discount <= 5 && List.fold((w, l) ->"
                + " if l.discount >= w then l.discount else w, %d, lines) <= 10, lines)"
                .formatted(BELOW)));
        assertTrue(another.contains("no IN point is owed at lines[*].discount = 100 (comparison@"),
                another);
        assertFalse(another.contains("lines[*].discount = 5 (comparison@"), another);
    }

    /**
     * A seed the input holds is one value of the run, which the end is kept of as of a seed
     * written out: what it may be is where the end starts. Taking every value, it is on both sides
     * of every discount on some run, and the comparison inside the step divides none; held at
     * fifty or more on the way, it is never passed by a discount at or below fifty, which parts
     * the discounts a row is owed at below eighty there.
     */
    @Test
    void theComparisonInsideTheStepReadsASeedTheInputHoldsAsWhereTheEndStarts() {
        String free = report(folded(GREATER, "base", "<= 10"));
        assertTrue(free.contains(RELATES_ANOTHER_VALUE), free);
        assertFalse(free.contains(NOT_SHOWN_TO_REACH), free);
        String held = report(model("base >= 50 && List.fold((w, l) -> %s, base, lines) <= 80"
                .formatted(GREATER)));
        assertFalse(held.contains(NOT_SHOWN_TO_REACH), held);
        assertTrue(held.contains("read as approval/lines[*].discount: in 50 < lines[*].discount"
                + " < 80"), held);
    }

    /**
     * A rule of the list that reads its elements may tie one element to another: the comparison
     * inside the step is said not to be worked out.
     */
    @Test
    void theComparisonInsideTheStepIsNotReadWhereTheElementsMayBeTied() {
        String related = report("""
                module example.worst

                data Line = { discount: Int }
                data Quote = { lines: List<Line> }
                    invariant List.all(l -> l.discount <= 50, lines)

                data Within
                data Needs

                behavior approval : (quote: Quote) -> Within | Needs

                let approval (quote) =
                    if List.fold((w, l) -> %s, 0, quote.lines) <= 10 then Within else Needs
                """.formatted(GREATER));
        assertTrue(related.contains(NOT_SHOWN_TO_REACH), related);
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
            assertTrue(report.contains(ON_ITS_RUNS), () -> step + ": " + report);
        }
    }

    /** What the walk walks has to be the list itself: over what a filter kept, every element is
     *  not every element of the list. */
    @Test
    void aWalkOverWhatAFilterKeptIsNotReadAsEveryElementOfTheList() {
        String report = report(model("List.fold((w, l) -> %s, 0, List.filter(l -> l.discount > 3,"
                .formatted(GREATER) + " lines)) <= 10"));
        assertTrue(report.contains(ON_ITS_RUNS), report);
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
                model("List.fold((w, l) -> %s, %d, lines) <= 10 && base > 3"
                        .formatted(GREATER, BELOW)));
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

    /** What it says of a fold read as keeping no end: what its runs worked out places the rows. */
    private static final String ON_ITS_RUNS =
            WhyAPlaceIsUndividedIsSaid.of(UndividedPosition.Reason.RULE_MEASURED_ON_ITS_RUNS);

    /** What it says of a relation to another value shown to divide none of the values here. */
    private static final String RELATES_ANOTHER_VALUE =
            "it relates the value here to another value rather than dividing the values here";

    /** And of one the other value is not shown to reach every value here for. */
    private static final String NOT_SHOWN_TO_REACH =
            "relates the value here to another value not shown to reach every value here";

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
    private record Drawn(String report, List<String> points, List<RowsOfABlock.Row> written) {

        /** What each row holds and answers, in order; what it is for is left out. */
        List<String> rows() {
            List<String> out = new ArrayList<>(written.stream().map(RowsOfABlock.Row::values).toList());
            out.sort(null);
            return out;
        }
    }

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
     * The rows written for what nothing covers. Two forms are held to the same rows by what each
     * holds and answers and not by what it is for: that names where the comparison is written, and
     * which of a form's rows a rule is composed onto is the form's.
     */
    private static List<RowsOfABlock.Row> rowsOf(Compilation compilation) {
        return RowsOfABlock.of(GeneratedRows.of(compilation, null, null,
                SourceRendering.namedByIdentity(SourceLayouts.NONE)).text());
    }

    private static String report(String model) {
        return reportOf(compiled(model));
    }

    private static String reportOf(Compilation compilation) {
        return AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
    }

    /**
     * Each model compiled once for the class. Several questions here are asked of the same walk —
     * what it is read as, what the report says of it, what the comparison inside it divides — and
     * each only reads the compilation.
     */
    private static final Map<String, Compilation> COMPILED = new ConcurrentHashMap<>();

    /** And given back when the class is done with them, so the classes after it do not run above
     *  what this one kept. */
    @AfterAll
    static void released() {
        COMPILED.clear();
    }

    private static Compilation compiled(String model) {
        return COMPILED.computeIfAbsent(model,
                AFoldThatKeepsAnEndIsReadAsEveryOrSomeElementTest::compiledAfresh);
    }

    private static Compilation compiledAfresh(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(each -> each.diagnostic().code().toString()).toList(),
                () -> "the source compiles: " + model);
        return compilation;
    }
}
