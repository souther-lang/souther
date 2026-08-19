package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.check.BehaviorContract;
import souther.compiler.check.Carrier;
import souther.compiler.inputs.BoundaryDomain;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.check.Clause;
import souther.compiler.check.ClauseName;
import souther.compiler.check.RuleRef;
import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A line the report names says which of a border's two points it is.
 *
 * <p>Both are values a row is owed at one border and the numbers differ by one step, so a report
 * naming neither prints two lines a reader cannot tell apart. Which one a value is turns on whether
 * the border is closed or open — the same {@code AT} is the {@code ON} point of {@code <= 100} and
 * the {@code OFF} point of {@code < 100} — so it cannot be read off the value or off which side of
 * the cut it sits (spec §example-report-vocabulary, §a-border-says-which-point-it-owes).
 *
 * <p>Measured with a closed border against an open one, differing in the operator alone. An absolute
 * expectation on one of them would pass against a report that answered {@code ON} everywhere, which
 * is what the answer was before it was derived at all.
 */
class ABorderSaysWhichOfItsTwoPointsALineIsTest {

    /** {@code <=}: the line's own values satisfy the rule, so 100 is inside and 101 is the step out. */
    private static final String CLOSED = model("<=");

    /** {@code <}: they do not, so 100 is outside and the point inside is the step back to 99. */
    private static final String OPENED = model("<");

    private static String model(String op) {
        return """
                module example.border

                data Ok
                data No
                data Result = Ok | No

                behavior sized : (n: Int) -> Result
                    constructs Ok, No

                let sized (n) =
                    if n %s 100 then Ok else No

                example sized
                    | "small" : (1) -> Ok
                """.formatted(op);
    }

    /**
     * The two points of a closed border, named for what they are.
     *
     * <p>100 satisfies {@code n <= 100} and so lies inside the partition the border bounds; 101 is
     * the first value outside it.
     */
    @Test
    void aClosedBorderIsAtItsOwnOnPoint() {
        String report = report(CLOSED);

        assertTrue(report.contains("no row is at the ON point sized/n = 100"), report);
        assertTrue(report.contains("no row is at the OFF point sized/n = 101"), report);
    }

    /**
     * The same border written {@code <}, where both answers move.
     *
     * <p>Not merely a different pair of numbers. 100 is still the value the rule names and is now the
     * point outside, and the point inside is 99 — so a reader told only that a row is missing at 100
     * is told the same thing about two rules that ask for opposite things.
     */
    @Test
    void anOpenBorderIsAtItsOwnOffPoint() {
        String report = report(OPENED);

        assertTrue(report.contains("no row is at the OFF point sized/n = 100"), report);
        assertTrue(report.contains("no row is at the ON point sized/n = 99"), report);
    }

    /**
     * The value alone does not say it, which is what the pair is here to show.
     *
     * <p>Both models name 100. The role differs, so a report that printed the value and not the role
     * would answer these two rules identically — and an assertion written against one of them alone
     * would hold against a report that never derived the role at all.
     */
    @Test
    void theSameValueIsTheOtherPointUnderTheOtherOperator() {
        assertTrue(report(CLOSED).contains("the ON point sized/n = 100"), report(CLOSED));
        assertTrue(report(OPENED).contains("the OFF point sized/n = 100"), report(OPENED));
    }

    /**
     * The JSON writes the four items under the border that owes them, each with what it asks for.
     *
     * <p>The role and the relation are two questions. {@code point} says what a row written there is
     * for; {@code relation} and {@code against} say what the row has to do, and the same {@code = 100}
     * is the {@code on} point of one of these models and the {@code off} point of the other. Neither
     * produces the other, and a document carrying one of them would be asking its reader to work out
     * the closed-border rule for themselves.
     */
    @Test
    void theJsonWritesEveryPointUnderItsBorder() {
        assertEquals(List.of("on:= 100", "off:= 101", "in:< 100", "out:> 101"),
                pointsAsked(CLOSED));
        assertEquals(List.of("on:= 99", "off:= 100", "in:< 99", "out:> 100"),
                pointsAsked(OPENED));
    }

    /**
     * A bound's point comes from the end it was placed at.
     *
     * <p>A discrete carrier steps a strict bound onto the value it leaves, so {@code value > 5}
     * bounds an {@code Int} at 6 — a value the type admits, and the {@code ON} point. The rule is
     * written {@code >} and the answer is {@code ON}, which is the operator and the answer
     * disagreeing: what settles it is where the end came to rest, and a bound read off its operator
     * would call this the {@code OFF} point and send an author after a 5 the type refuses.
     */
    @Test
    void aBoundsPointComesFromItsEndAndNotFromItsOperator() {
        String report = report(bounded("Int", "> 5"));

        assertTrue(report.contains("the ON point take/h.a = 6"), report);
        assertFalse(report.contains("take/h.a = 5"), report);
    }

    /**
     * A bound owes one point, and its spelling moves where that point is rather than what it is.
     *
     * <p>The invariant path answered from an operator would put these two at one value and tell them
     * apart by the role — which is what a guard's border does and what a bound's does not. A bound
     * leaves nothing outside itself, so there is no value over the line for a row to be at: the
     * spelling is spent moving the end, and both ends that arrive are inside.
     *
     * <p>Written as a pair for the same reason the guard tests are. An expectation on {@code >= 5}
     * alone holds against a reader that ignores the end and answers 5 for both, and one on {@code >
     * 5} alone holds against a reader that ignores the operator.
     */
    @Test
    void aBoundsSpellingMovesItsPointRatherThanChangingWhichPointItIs() {
        String closed = report(bounded("Int", ">= 5"));
        String strict = report(bounded("Int", "> 5"));

        assertTrue(closed.contains("the ON point take/h.a = 5"), closed);
        assertTrue(strict.contains("the ON point take/h.a = 6"), strict);
        // And neither owes a row over the line. A bound leaves nothing outside itself, so the two
        // points out there are excluded — said in those words rather than left out, because a border
        // showing two of four items and nothing beside them reads as this compiler being short.
        for (String report : List.of(closed, strict)) {
            assertTrue(report.contains(
                    "no OFF point is owed"), report);
            assertTrue(report.contains(
                    "no OUT point is owed"), report);
            assertTrue(report.contains("excluded — the rules leave no value there"), report);
            assertFalse(report.contains("no row is at the OFF point"), report);
        }
        assertFalse(strict.contains("take/h.a = 5"), strict);
    }

    /**
     * The end is read rather than assumed closed, at the one place both kinds are built.
     *
     * <p>A continuous carrier has no step to take, so {@code value > 5.0m} on a {@code Decimal}
     * reaches {@link OriginRef.InvariantOrigin} as an exclusive 5 — measured at the construction
     * site, where both kinds arrive. No report shows one: such a cut is dropped further down. That
     * makes the closed end a fact about how far the derivation gets rather than about bounds, and
     * an origin that assumed it would answer {@code ON} for a value its own type refuses on the day
     * the derivation reaches further.
     */
    @Test
    void aBoundThatStopsShortOfItsValueDrawsNoBorderAtIt() {
        assertEquals(Criterion.AtThePlace.class,
                borderOf(new OriginRef.InvariantOrigin(invariant(), true))
                        .demand(PointRole.ON).criterion().getClass(),
                "a bound that admits its own end is at that end's ON point");
        // And where it does not admit it, the position does not reach the line: the value is outside
        // what the rules leave, so there is no border here and no point of one either. Read as a
        // border, it would owe an ON point one step in that no carrier here names.
        assertEquals(null, borderOf(new OriginRef.InvariantOrigin(invariant(), false)),
                "a bound whose own end its position refuses draws no line at it");
    }

    /** The border a bound draws at 5 on an `Int` whose rules leave 5 and up. */
    private static Border borderOf(OriginRef origin) {
        Carrier carrier = new Carrier.Whole();
        boolean admits = origin instanceof OriginRef.InvariantOrigin bound && bound.holdsAtTheValue();
        return Border.atAPlace(new AxisId("take", "h.a"),
                Cut.at(carrier, Count.of(5), origin),
                origin, BoundaryDomain.on(carrier),
                new NumericDomain.Bounds(new Endpoint(Count.of(5), admits), null));
    }

    /**
     * The two roles are defined at the cut and at the value beside it, and refused anywhere else.
     *
     * <p>Under {@code <= 100} the value below the cut is 99, which is inside the partition and not
     * against its border — an {@code IN} point, and neither of the two words here. Answered by the
     * arithmetic alone it comes back {@code OFF}, which would say a value well inside the range is
     * outside it. What keeps the derivation honest is the domain rather than the formula, so a side
     * no rule places a row on is refused.
     *
     * <p>An invariant places a row on no side at all, so every side but the cut is refused there.
     */
    @Test
    void aSideNoRowIsOwedOnIsNamedRatherThanGivenTheNearerWord() {
        // `<= 100`: the cut belongs to the passing side, so the row beside it is the one above, and
        // the value below the cut is 99 — inside the partition and away from its border, which is
        // the IN point and neither of the two words against the line.
        Carrier carrier = new Carrier.Whole();
        OriginRef closed = new OriginRef.EnsuresOrigin(
                new RuleRef.Ensures(new BehaviorContract.RuleId(null, 0, 0, null), "cap"),
                true, true, false);
        Border border = Border.atAPlace(new AxisId("cap", "n"),
                Cut.at(carrier, Count.of(100), closed), closed, BoundaryDomain.on(carrier),
                new NumericDomain.Bounds(null, null));

        assertEquals("= 100", border.demand(PointRole.ON).criterion().asked(border.cut()));
        assertEquals("= 101", border.demand(PointRole.OFF).criterion().asked(border.cut()));
        assertEquals("< 100", border.demand(PointRole.IN).criterion().asked(border.cut()),
                "99 is inside the partition and away from the border, which is the IN point");
        assertEquals("> 101", border.demand(PointRole.OUT).criterion().asked(border.cut()));

        // A bound owes nothing outside itself, and says which of the three answers settled it.
        Border bound = borderOf(new OriginRef.InvariantOrigin(invariant(), true));
        assertEquals(new Demand.NotOwed(NotOwedReason.THE_RULES_REFUSE_IT),
                bound.demand(PointRole.OFF));
        assertEquals(new Demand.NotOwed(NotOwedReason.THE_RULES_REFUSE_IT),
                bound.demand(PointRole.OUT));
        assertEquals("/= 5", bound.demand(PointRole.IN).criterion().asked(bound.cut()),
                "and everything else the position admits is inside the bound");
    }

    /** The clause the bound tests name, which is only an identity here. */
    private static RuleRef.Invariant invariant() {
        return new RuleRef.Invariant(new Clause.Ref(
                new Clause.Id(TypeSymbols.declared(new TypeKey("example.bound", "Above")), 0),
                Optional.of(new ClauseName("above"))));
    }

    /** A newtype bounded by {@code rule}, held in a record, with one row well away from the bound. */
    private static String bounded(String carrier, String rule) {
        return """
                module example.bound

                data Above = %s
                    invariant above = value %s

                data Holder = { a: Above }

                data Ok

                behavior take : (h: Holder) -> Ok
                    constructs Ok

                let take (h) = Ok

                example take
                    | "away from the bound" : (Holder { a = Above(%s) }) -> Ok
                """.formatted(carrier, rule, "Int".equals(carrier) ? "30" : "30.0m");
    }

    /**
     * The combination counts are not on the border's line, nor on the partition's.
     *
     * <p>Counting combinations across two positions is the neighbouring technique. Printed at the end
     * of the partition line it sat beside the border counts, where the two read as parts of one
     * total.
     */
    @Test
    void combinationsAreCountedOnALineOfTheirOwn() {
        String report = report(CLOSED);

        for (String line : report.lines().toList()) {
            if (line.contains("pairs ")) {
                assertTrue(line.trim().startsWith("combination "), report);
            }
            assertFalse(line.contains("partition ") && line.contains("pairs "), report);
        }
    }

    /** Held so a rename of the report's own words does not turn the assertions above into ones that
     *  pass on a report saying nothing. */
    @Test
    void theReportStillNamesTheMeasuresTheseAssertionsRead() {
        String report = report(CLOSED);

        assertEquals(1, report.split("    border ", -1).length - 1, report);
        assertEquals(1, report.split("    partition ", -1).length - 1, report);
    }

    /** Each item of the model's borders as {@code point:relation against}, in document order. */
    private static List<String> pointsAsked(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        JsonNode root = JsonMapper.builder().build()
                .readTree(AdequacyReport.of(compilation).json(SourceNameResolver.identity()));
        List<String> out = new ArrayList<>();
        root.findValues("boundaries").forEach(each -> each.forEach(
                b -> b.get("items").forEach(i -> out.add(i.get("point").asText() + ":"
                        + i.get("relation").asText() + " " + i.get("against").asText()))));
        return out;
    }

    private static String report(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).human(SourceNameResolver.identity());
    }
}
