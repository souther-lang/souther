package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.EnumMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A border owes a row at four points, and where it owes none it says which of three things settled
 * that.
 *
 * <p>Every one of these used to be a coverage item that was never built. The obligation was left out
 * of a list, and all of them reached a reader as the same thing — one fewer entry — so a reader
 * counting the four items the technique asks for found this compiler short and was never told which
 * of them had happened. Two of the three are not shortfalls at all: the rules refusing the point is
 * the model having discharged it, and a carrier naming no value one step over is an item that cannot
 * exist.
 *
 * <p>Each reason is measured against a model that differs from it in one thing and owes the row. An
 * expectation on one model alone holds against a reader that answers "not owed" everywhere, which is
 * exactly what leaving the entry out amounted to.
 */
class ABorderSaysWhyItOwesNoRowAtAPointTest {

    /** A newtype bounded by {@code rule}, held in a record, with a guard at {@code guard} on it. */
    private static String model(String carrier, String rule, String guard, String row) {
        return """
                module example.owed

                data A = %s
                    invariant bound = value %s

                data H = { a: A }

                data Ok
                data No
                data Verdict = Ok | No

                behavior take : (h: H) -> Verdict
                    constructs Ok, No
                let take (h) = { guard h.a.value %s else Ok
                    No }

                example take
                    | "one" : (H { a = A(%s) }) -> No
                """.formatted(carrier, rule, guard, row);
    }

    /**
     * A bound owes nothing outside itself, and a guard at the same value owes the step over.
     *
     * <p>The pair is the measurement. Both borders are on one position and one is at the very value
     * the other is, so what differs between the two answers is which rule drew the line — which is
     * the whole of what decides whether there is a far side at all.
     */
    @Test
    void theRulesRefuseThePointsOutsideABound() {
        Map<String, BorderAssessment> borders = bordersOf(model("Int", ">= 0", "<= 100", "50"));

        BorderAssessment bound = borders.get("h.a = 0");
        assertNotNull(bound, borders.keySet().toString());
        assertEquals(new souther.compiler.query.ItemAssessment.NotOwed(
                        NotOwedReason.THE_RULES_REFUSE_IT), bound.at(PointRole.OFF));
        assertEquals(new souther.compiler.query.ItemAssessment.NotOwed(
                        NotOwedReason.THE_RULES_REFUSE_IT), bound.at(PointRole.OUT));

        BorderAssessment guard = borders.get("h.a = 100");
        assertNotNull(guard, borders.keySet().toString());
        assertEquals("101", guard.against(PointRole.OFF),
                "a guard leaves values either side, so the step over is a row somebody is owed");
        assertEquals("> 101", guard.operator(PointRole.OUT) + " " + guard.against(PointRole.OUT));
    }

    /**
     * A carrier with no next value names no point one step over, and one that has a next value does.
     *
     * <p>Told apart from the reason above rather than folded into it. This one is a limit of what
     * the language can write down; that one is the model refusing the value. A reader handed the
     * second about a point the rules refuse would go looking for a missing conversion.
     */
    @Test
    void aCarrierWithNoNextValueNamesNoPointBesideTheLine() {
        assertEquals("101",
                bordersOf(model("Int", ">= 0", "<= 100", "50")).get("h.a = 100")
                        .against(PointRole.OFF),
                "a whole number has a next one");
        assertEquals(new souther.compiler.query.ItemAssessment.NotOwed(
                        NotOwedReason.THE_CARRIER_NAMES_NO_NEIGHBOUR),
                bordersOf(model("Decimal", ">= 0m", "<= 100m", "50m")).get("h.a = 100")
                        .at(PointRole.OFF),
                "and a decimal has none, so the point one step over is not named at all");
    }

    /**
     * An equality names a value and orders nothing around it, so neither neighbour is the nearer.
     *
     * <p>Against an ordering at the same value, where the neighbour is exactly what the rule places.
     * What the equality does divide is the value from every other value, and that is what its
     * {@code OUT} point is for — reported as one thing the border owes rather than as a class of the
     * partition beside it.
     */
    @Test
    void aRuleThatNamesAValueOwesNoPointBesideIt() {
        BorderAssessment singled = bordersOf(model("Int", ">= 0", "== 100", "50")).get("h.a = 100");
        assertEquals(new souther.compiler.query.ItemAssessment.NotOwed(
                        NotOwedReason.THE_RULE_NAMES_A_VALUE_NOT_A_SIDE), singled.at(PointRole.OFF));
        assertEquals("/= 100",
                singled.operator(PointRole.OUT) + " " + singled.against(PointRole.OUT),
                "what it divides is the value from every other value");

        assertEquals("101",
                bordersOf(model("Int", ">= 0", "<= 100", "50")).get("h.a = 100")
                        .against(PointRole.OFF),
                "an ordering at the same value places the neighbour the equality does not");
    }

    /**
     * A side the rules leave one value wide has no point away from the border.
     *
     * <p>The same reason as a bound's far side, one arity up: every value an {@code IN} point could
     * be written at is one the rules refuse. Against a guard three values further out, where the
     * side holds values and the point is owed.
     */
    @Test
    void aSideTheRulesLeaveOneValueWideOwesNoPointAwayFromTheBorder() {
        assertEquals(new souther.compiler.query.ItemAssessment.NotOwed(
                        NotOwedReason.THE_RULES_REFUSE_IT),
                bordersOf(model("Int", ">= 0", "<= 0", "0")).get("h.a = 0").at(PointRole.IN),
                "nothing is inside `0 <= x <= 0` and away from its border");
        assertEquals("< 3",
                inside(bordersOf(model("Int", ">= 0", "<= 3", "1")).get("h.a = 3")),
                "and three values further out the side holds values");
    }

    /**
     * A line between two positions divides neither of them and still has two sides.
     *
     * <p>Left to the measure that counts a position's classes, such a line had no {@code IN} point
     * and no {@code OUT} point anywhere: neither position is divided, so there is no class for
     * either to be a row in. Keyed on the border they are ordinary — a row where the two fall apart
     * one way is inside it and one where they fall apart the other way is outside.
     */
    @Test
    void aLineBetweenTwoPositionsOwesBothSidesOfItself() {
        BorderAssessment line = bordersOf("""
                module example.owed

                data P = { a: Int, b: Int }

                data Ok
                data No
                data Verdict = Ok | No

                behavior cmp : (p: P) -> Verdict
                    constructs Ok, No
                let cmp (p) = { guard p.a < p.b else Ok
                    No }

                example cmp
                    | "under" : (P { a = 1, b = 2 }) -> No
                """).get("p.a = p.b");

        assertNotNull(line);
        assertEquals("< p.b", inside(line), "a row under the line is inside the border");
        assertEquals("> p.b",
                line.operator(PointRole.OUT) + " " + line.against(PointRole.OUT));
        // `<` is open at the line, so the row where the two are equal is the border's OFF point,
        // and the ON point one step in is on the difference — which neither position has a
        // neighbour at.
        assertEquals("= p.b", line.operator(PointRole.OFF) + " " + line.against(PointRole.OFF));
        assertEquals(new souther.compiler.query.ItemAssessment.NotOwed(
                        NotOwedReason.THE_CARRIER_NAMES_NO_NEIGHBOUR), line.at(PointRole.ON),
                "the step in is on the difference, which neither position has a neighbour at");
    }

    /**
     * A border answers for every role, and one that does not cannot be built.
     *
     * <p>Held at the constructor rather than by walking what a corpus happens to produce. Every
     * reason above was once an entry left out of a list, and a list is a shape in which leaving one
     * out is not an error — so the answer is that the shape refuses it.
     */
    @Test
    void aBorderThatAnswersForSomeRolesAndNotOthersCannotBeBuilt() {
        for (BorderAssessment each
                : bordersOf(model("Int", ">= 0", "<= 100", "50")).values()) {
            assertEquals(java.util.EnumSet.allOf(PointRole.class), each.items().keySet(),
                    each.label());
            assertEquals(java.util.EnumSet.allOf(PointRole.class),
                    each.border().demands().keySet(), each.label());
        }

        Border whole = bordersOf(model("Int", ">= 0", "<= 100", "50")).get("h.a = 100").border();
        Map<PointRole, Demand> short_ = new EnumMap<>(PointRole.class);
        short_.put(PointRole.ON, whole.demand(PointRole.ON));
        assertThrows(IllegalArgumentException.class,
                () -> new Border(whole.cut(), whole.origin(), short_));
    }

    /**
     * The report says the reason in words, and says it apart from a row nobody has written.
     *
     * <p>The whole point of the three reasons is what a reader does about them, so the line that
     * carries one is not marked as a gap and does not read as one.
     */
    @Test
    void theReportSaysWhyAPointIsNotOwed() {
        String report = report(model("Int", ">= 0", "<= 100", "50"));

        assertTrue(report.contains(
                "no OFF point is owed at h.a = 0 (invariant A (bound)): excluded — the rules leave no"
                        + " value there"), report);
        assertTrue(report.contains(
                "no OUT point is owed at h.a = 0 (invariant A (bound)): excluded — the rules leave no"
                        + " value there"), report);
        assertFalse(report.contains("no row is at the OFF point h.a = 0"), report);
    }

    /**
     * A point a row already sits at is not a point a search came back empty from.
     *
     * <p>The two answers are about different things and both reach an author: what the rows showed
     * is a verdict, and what was tried is what {@code --generate} prints. A side of a line between
     * two positions is the one point this compiler composes nothing for, and answered as a search
     * that ran and failed it put a reason under every such side on every run — including the sides a
     * row is in and the sides nothing measured, which is the specific work a person is handed that
     * they may already have done.
     */
    @Test
    void aPointARowIsAlreadyAtIsNotOneASearchCameBackEmptyFrom() {
        Map<String, BorderAssessment> borders = bordersOf(BOTH_SIDES);
        BorderAssessment line = borders.get("p.a = p.b");
        assertNotNull(line, borders.keySet().toString());

        assertTrue(line.owedAt(PointRole.IN).coverage().hit(), "a row is under the line");
        assertTrue(line.owedAt(PointRole.OUT).coverage().hit(), "and one is over it");
        for (PointRole role : List.of(PointRole.IN, PointRole.OUT)) {
            assertEquals(souther.compiler.query.ItemAssessment.Attempt.Reason
                            .A_ROW_IS_ALREADY_THERE,
                    assertInstanceOf(souther.compiler.query.ItemAssessment.Attempt.NotAttempted.class,
                            line.owedAt(role).attempt(), role.toString()).reason(),
                    role.toString());
        }

        // And the block an author reads says nothing about them, because nothing is owed there.
        String block = souther.compiler.report.GeneratedRows.of(
                compiled(BOTH_SIDES), "example.owed", "cmp", true, SourceNameResolver.identity());
        assertFalse(block.contains("p.a < p.b"), block);
        assertFalse(block.contains("p.a > p.b"), block);
    }

    /** A line between two positions with a row either side of it and none on it. */
    private static final String BOTH_SIDES = """
            module example.owed

            data P = { a: Int, b: Int }

            data Ok
            data No
            data Verdict = Ok | No

            behavior cmp : (p: P) -> Verdict
                constructs Ok, No
            let cmp (p) = { guard p.a < p.b else Ok
                No }

            example cmp
                | "under" : (P { a = 1, b = 2 }) -> No
                | "over" : (P { a = 2, b = 1 }) -> Ok
            """;

    /** What a row inside this border has to do, as the report writes it. */
    private static String inside(BorderAssessment border) {
        return border.operator(PointRole.IN) + " " + border.against(PointRole.IN);
    }

    /** Every border of the one behavior {@code model} declares, by the line it is at. */
    private static Map<String, BorderAssessment> bordersOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> boundaries =
                compilation.db().ask(new Adequacy.Boundaries("example.owed")).value();
        assertNotNull(boundaries, "the model under test compiles");
        Map<String, BorderAssessment> out = new java.util.LinkedHashMap<>();
        boundaries.values().forEach(each -> each.forEach(b -> out.put(b.label(), b)));
        return out;
    }

    private static String report(String model) {
        return AdequacyReport.of(compiled(model)).human(SourceNameResolver.identity());
    }

    private static Compilation compiled(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return compilation;
    }
}
