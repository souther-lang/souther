package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Towards;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule holding a quantity over several positions at one value is measured on a line over that
 * quantity, as an order on it is.
 *
 * <p>No position holds the value as a class of its own, so the line is the only place the rule is
 * measured at: the rows where the quantity comes to the value, the nearest ones either side, and
 * the runs past those. Which of them a row can be written at is what the positions reach, read
 * against the quantity as a whole — two sets of a three-case element each hold three at most, so
 * their sizes come to six only where both hold every case, and to nothing above six at all.
 *
 * <p>Only where the quantity counts. Two strings stand no number apart, so a rule holding them
 * equal has no value beside the one it names, and is no line.
 */
class AValueSingledOutOnAQuantityOverPositionsIsALineTest {

    private static final String SETS = """
            module m

            data Service = Insurance | Support | Security

            behavior both : (a: Set<Service>, b: Set<Service>) -> Int
            let both (a, b) = if %s then 1 else 0
            """;

    private static final String INTS = """
            module m

            behavior both : (a: Int, b: Int) -> Int
            let both (a, b) = if %s then 1 else 0
            """;

    private static final String HELD = """
            module m

            data R = { x: Int, y: Int }
              invariant x >= 0 && y >= 0 && x + y <= 4

            behavior both : (r: R) -> Int
            let both (r) = if %s then 1 else 0
            """;

    /** Six only where both sets hold every case, and nothing above it. */
    @Test
    void theSizesOfTwoSetsComeToTheValueOnlyWhereBothHoldEveryCase() {
        Map<DomainPoint, String> points = atEachPoint(SETS, "Set.size(a) + Set.size(b) == 6",
                AValueSingledOutOnAQuantityOverPositionsIsALineTest::sizes);

        assertEquals("3 + 3", points.get(new DomainPoint.AtTheLine()));
        assertEquals(5, sum(points.get(new DomainPoint.BesideTheLine(Towards.BELOW))));
        assertEquals(REFUSED, points.get(new DomainPoint.BesideTheLine(Towards.ABOVE)));
        assertEquals(REFUSED, points.get(new DomainPoint.InTheRegion(Towards.ABOVE)));
        assertTrue(sum(points.get(new DomainPoint.InTheRegion(Towards.BELOW))) < 5,
                () -> "the run below the nearest value is below it: " + points);
    }

    /** One below what the two can reach together has a row either side of it. */
    @Test
    void aValueBelowTheMostTheyComeToHasARowEitherSide() {
        Map<DomainPoint, String> points = atEachPoint(SETS, "Set.size(a) + Set.size(b) == 5",
                AValueSingledOutOnAQuantityOverPositionsIsALineTest::sizes);

        assertEquals(5, sum(points.get(new DomainPoint.AtTheLine())));
        assertEquals(4, sum(points.get(new DomainPoint.BesideTheLine(Towards.BELOW))));
        assertEquals(6, sum(points.get(new DomainPoint.BesideTheLine(Towards.ABOVE))));
        assertEquals(REFUSED, points.get(new DomainPoint.InTheRegion(Towards.ABOVE)));
    }

    /** A value the two never come to names no place, and no line is drawn there. */
    @Test
    void aValueTheyNeverComeToDrawsNoLine() {
        assertEquals(List.of(), lines(SETS, "Set.size(a) + Set.size(b) == 7"));
    }

    /**
     * The value beside the one named is the nearest the quantity comes to, which a weight on each
     * position moves: twice each size comes to twelve and then to ten.
     */
    @Test
    void theValueBesideItIsTheNearestTheWeightsLetTheQuantityComeTo() {
        Map<DomainPoint, String> points = atEachPoint(SETS,
                "2 * Set.size(a) + 2 * Set.size(b) == 12",
                AValueSingledOutOnAQuantityOverPositionsIsALineTest::sizes);

        assertEquals("3 + 3", points.get(new DomainPoint.AtTheLine()));
        assertEquals(5, sum(points.get(new DomainPoint.BesideTheLine(Towards.BELOW))));
        assertEquals(REFUSED, points.get(new DomainPoint.BesideTheLine(Towards.ABOVE)));
    }

    /** Which position a rule names first is no part of the quantity. */
    @Test
    void theOrderThePositionsAreWrittenInChangesNothing() {
        assertEquals(atEachPoint(SETS, "Set.size(a) + Set.size(b) == 6",
                        AValueSingledOutOnAQuantityOverPositionsIsALineTest::sizes),
                atEachPoint(SETS, "Set.size(b) + Set.size(a) == 6",
                        AValueSingledOutOnAQuantityOverPositionsIsALineTest::sizes));
    }

    /**
     * Two numbers held equal are a line on how far apart they stand: where they meet, and one
     * either way. A disequality places the same line.
     */
    @Test
    void twoNumbersHeldEqualAreALineOnHowFarApartTheyStand() {
        Map<DomainPoint, String> points = atEachPoint(INTS, "a == b",
                AValueSingledOutOnAQuantityOverPositionsIsALineTest::apart);

        assertEquals("0", points.get(new DomainPoint.AtTheLine()));
        assertEquals("-1", points.get(new DomainPoint.BesideTheLine(Towards.BELOW)));
        assertEquals("1", points.get(new DomainPoint.BesideTheLine(Towards.ABOVE)));
        assertEquals(points, atEachPoint(INTS, "a /= b",
                AValueSingledOutOnAQuantityOverPositionsIsALineTest::apart));
    }

    /**
     * A disequality places the line an equality does with the roles turned: the row where the two
     * meet is outside what the rule holds at, and the ones beside it inside.
     */
    @Test
    void aDisequalityTurnsTheRolesOfThePointsAnEqualityHas() {
        Border equal = onlyLine(INTS, "a == b");
        Border apart = onlyLine(INTS, "a /= b");
        DomainPoint on = new DomainPoint.AtTheLine();
        DomainPoint below = new DomainPoint.BesideTheLine(Towards.BELOW);
        DomainPoint above = new DomainPoint.BesideTheLine(Towards.ABOVE);

        assertEquals(List.of(PointRole.ON, PointRole.OFF, PointRole.OFF),
                List.of(equal.roleOf(on), equal.roleOf(below), equal.roleOf(above)));
        assertEquals(List.of(PointRole.OFF, PointRole.ON, PointRole.ON),
                List.of(apart.roleOf(on), apart.roleOf(below), apart.roleOf(above)));
    }

    /**
     * A run beside one line on a quantity stops at the next line on it, whichever of the two names
     * a value and whichever orders the values.
     *
     * <p>Between a rule at three and one at five there is only four, which is the nearest value to
     * each of them and their own point, so neither has a run on the side facing the other. Read
     * past the next line, a row there would be a row of another class, counted for this one.
     */
    @Test
    void aRunBesideALineStopsAtTheNextLineOnTheSameQuantity() {
        Map<Integer, Map<Towards, String>> sets = regionsByLine("""
                module m

                data Service = Insurance | Support | Security

                behavior both : (a: Set<Service>, b: Set<Service>) -> Int
                let both (a, b) = if Set.size(a) + Set.size(b) == 3 then 1
                    else if Set.size(a) + Set.size(b) == 5 then 2 else 0
                """, AValueSingledOutOnAQuantityOverPositionsIsALineTest::sizes);
        assertEquals(REFUSED, sets.get(3).get(Towards.ABOVE), () -> "" + sets);
        assertEquals(REFUSED, sets.get(5).get(Towards.BELOW), () -> "" + sets);
        assertTrue(sum(sets.get(3).get(Towards.BELOW)) < 2, () -> "below the nearest: " + sets);

        Map<Integer, Map<Towards, String>> ints = regionsByLine("""
                module m

                behavior both : (a: Int, b: Int) -> Int
                let both (a, b) = if a + b == 3 then 1 else if a + b < 5 then 2 else 0
                """, AValueSingledOutOnAQuantityOverPositionsIsALineTest::added);
        assertEquals(REFUSED, ints.get(3).get(Towards.ABOVE), () -> "" + ints);
        assertEquals(REFUSED, ints.get(5).get(Towards.BELOW),
                () -> "the order's run below stops at the value singled out: " + ints);
        assertTrue(sum(ints.get(3).get(Towards.BELOW)) < 2, () -> "below the nearest: " + ints);
        assertTrue(sum(ints.get(5).get(Towards.ABOVE)) > 5, () -> "above the line: " + ints);
    }

    /** And with a third line on the quantity, each run stops at whichever line is next to it. */
    @Test
    void aRunStopsAtTheNextLineWhereThereAreSeveral() {
        Map<Integer, Map<Towards, String>> ints = regionsByLine("""
                module m

                behavior both : (a: Int, b: Int) -> Int
                let both (a, b) = if a + b == 3 then 1 else if a + b == 5 then 2
                    else if a + b < 6 then 3 else 0
                """, AValueSingledOutOnAQuantityOverPositionsIsALineTest::added);
        assertEquals(REFUSED, ints.get(3).get(Towards.ABOVE), () -> "" + ints);
        assertEquals(REFUSED, ints.get(5).get(Towards.BELOW), () -> "" + ints);
        assertEquals(REFUSED, ints.get(6).get(Towards.BELOW),
                () -> "the order's run below stops at the value five singles out: " + ints);
        assertTrue(sum(ints.get(6).get(Towards.ABOVE)) > 6, () -> "above the line: " + ints);
    }

    /**
     * Two strings held equal are no line, where the same two held in an order are one: they stand
     * no number apart, and the only value their distance takes is where they meet.
     */
    @Test
    void twoStringsHeldEqualAreNoLine() {
        String model = """
                module m

                data Id = String
                  invariant String.length(value) >= 1

                behavior both : (a: Id, b: Id) -> Int
                let both (a, b) = if %s then 1 else 0
                """;
        assertEquals(List.of(), ofTheComparison(model, "a == b"));
        assertEquals(List.of(), ofTheComparison(model, "a /= b"));
        assertEquals(1, ofTheComparison(model, "a < b").size());
    }

    /**
     * Whether the quantity comes to the value is asked of the positions together. Each of these
     * reaches six on its own, and the declaration keeps the two at four between them.
     */
    @Test
    void whetherTheQuantityComesToTheValueIsAskedOfThePositionsTogether() {
        assertFalse(lines(HELD, "r.x + r.y == 6").stream()
                        .anyMatch(each -> each.border().origin()
                                instanceof LineOrigin.ComparisonOrigin),
                "the declaration's lines are drawn, and none for the comparison");
        Map<DomainPoint, String> points = comparisonPoints(HELD, "r.x + r.y == 4");
        assertEquals(REFUSED, points.get(new DomainPoint.BesideTheLine(Towards.ABOVE)));
        assertEquals("R { x = 0, y = 4 }", points.get(new DomainPoint.AtTheLine()));
    }

    /**
     * A declaration naming one value of the quantity, held equal or apart, is no line. A line a
     * declaration draws is an end of what it admits, and such a clause keeps no end, so only the
     * body's own rule is measured.
     */
    @Test
    void aDeclarationHoldingTheQuantityAtOneValueDrawsNoLine() {
        String model = """
                module m

                data R = { x: Int, y: Int }
                  invariant %s

                behavior both : (r: R) -> Int
                let both (r) = if r.x >= 3 then 1 else 0
                """;
        for (String clause : List.of("x + y == 6", "x == y", "x /= y")) {
            List<BorderAssessment> lines = lines(model, clause);
            assertEquals(1, lines.size(), () -> clause + ": " + lines);
            assertTrue(lines.get(0).border().origin() instanceof LineOrigin.ComparisonOrigin,
                    () -> clause + ": " + lines);
        }
    }

    private static final String REFUSED = "refused";

    /** What each point of the one line the rule draws comes to, read off the row built there. */
    private static Map<DomainPoint, String> atEachPoint(String model, String condition,
                                                        Function<List<String>, String> read) {
        List<BorderAssessment> lines = lines(model, condition);
        assertEquals(1, lines.size(), () -> condition + " draws one line: " + lines);
        return points(lines.get(0), read);
    }

    /** The same, of the comparison's line among the declaration's. */
    private static Map<DomainPoint, String> comparisonPoints(String model, String condition) {
        List<BorderAssessment> lines = ofTheComparison(model, condition);
        assertEquals(1, lines.size(), () -> condition + ": " + lines);
        return points(lines.get(0), inputs -> String.join(", ", inputs));
    }

    /** The lines the body's comparison draws, leaving out those of the declarations. */
    private static List<BorderAssessment> ofTheComparison(String model, String condition) {
        return lines(model, condition).stream()
                .filter(each -> each.border().origin() instanceof LineOrigin.ComparisonOrigin)
                .toList();
    }

    private static Map<DomainPoint, String> points(BorderAssessment line,
                                                   Function<List<String>, String> read) {
        Map<DomainPoint, String> out = new LinkedHashMap<>();
        line.items().forEach((point, item) -> out.put(point, switch (item) {
            case ItemAssessment.NotOwed notOwed
                    when notOwed.reason() == NotOwedReason.THE_RULES_REFUSE_IT -> REFUSED;
            case ItemAssessment.Owed owed -> owed.searches().each().stream()
                    .filter(ItemAssessment.Attempt.Certified.class::isInstance)
                    .map(ItemAssessment.Attempt.Certified.class::cast)
                    .findFirst()
                    .map(certified -> read.apply(certified.row().inputs().stream()
                            .map(FixtureTemplate::text).toList()))
                    .orElse("no row: " + owed);
            default -> item.toString();
        }));
        return out;
    }

    /** The border of the one line {@code condition} draws. */
    private static Border onlyLine(String model, String condition) {
        List<BorderAssessment> lines = lines(model, condition);
        assertEquals(1, lines.size(), () -> condition + " draws one line: " + lines);
        return lines.get(0).border();
    }

    /**
     * What each of the lines the body's comparisons draw leaves in the run either side of it, by
     * the level the line is at: refused, or what the row built there comes to.
     */
    private static Map<Integer, Map<Towards, String>> regionsByLine(
            String source, Function<List<String>, String> read) {
        Map<Integer, Map<Towards, String>> out = new LinkedHashMap<>();
        for (BorderAssessment line : linesOf(source)) {
            Map<DomainPoint, String> points = points(line, read);
            Map<Towards, String> sides = new LinkedHashMap<>();
            for (Towards side : Towards.values()) {
                sides.put(side, points.get(new DomainPoint.InTheRegion(side)));
            }
            out.put(Integer.parseInt(line.border().cut().at().asAnExactNumber().toString()), sides);
        }
        return out;
    }

    /** Two numbers, as {@code "3 + -2"}, which {@link #sum} adds up. */
    private static String added(List<String> inputs) {
        return String.join(" + ", inputs);
    }

    /** How many each of two sets holds, as {@code "3 + 2"}. */
    private static String sizes(List<String> inputs) {
        return inputs.stream().map(set -> set.equals("[]") ? "0"
                : String.valueOf(set.split(",").length)).reduce((one, two) -> one + " + " + two)
                .orElseThrow();
    }

    /** How far the first of two numbers stands above the second. */
    private static String apart(List<String> inputs) {
        return String.valueOf(Integer.parseInt(inputs.get(0)) - Integer.parseInt(inputs.get(1)));
    }

    /** What the numbers {@link #sizes} or {@link #added} read add up to, failing where the point
     *  held no row. */
    private static int sum(String sizes) {
        assertTrue(sizes != null && sizes.matches("-?\\d+( \\+ -?\\d+)*"),
                () -> "a row of two numbers, where the point is owed one: " + sizes);
        int out = 0;
        for (String each : sizes.split(" \\+ ")) {
            out += Integer.parseInt(each);
        }
        return out;
    }

    private static List<BorderAssessment> lines(String model, String condition) {
        return linesOf(model.formatted(condition));
    }

    private static List<BorderAssessment> linesOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).modules().get(0).behaviors().get(0).lines();
    }
}
