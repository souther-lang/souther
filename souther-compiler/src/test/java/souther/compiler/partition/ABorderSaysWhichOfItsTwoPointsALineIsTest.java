package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

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
     * The JSON carries the role beside the geometry rather than in place of it.
     *
     * <p>Two questions. {@code side} says where the value sits around the cut, which is what says how
     * to read {@code value}; {@code point} says what a row written there is for. Neither produces the
     * other: {@code at} is the {@code on} point of one of these models and the {@code off} point of
     * the other, and both documents write {@code at}.
     */
    @Test
    void theJsonWritesBothTheSideAndThePoint() {
        assertEquals(List.of("at/on", "above/off"), sidesAndPoints(CLOSED));
        assertEquals(List.of("at/off", "below/on"), sidesAndPoints(OPENED));
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
        // And neither owes the value over the line. `besideTheCut` answers nothing for a bound, so
        // an OFF point here would be a row asked for at a value the type refuses.
        assertFalse(closed.contains("OFF point"), closed);
        assertFalse(strict.contains("OFF point"), strict);
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
    void aBoundThatStopsShortOfItsValueIsTheOffPoint() {
        RuleRef.Invariant rule = new RuleRef.Invariant(new Clause.Ref(
                new Clause.Id(TypeSymbols.declared(new TypeKey("example.bound", "Above")), 0),
                Optional.of(new ClauseName("above"))));

        assertEquals(BoundaryObligation.PointRole.ON,
                BoundaryObligation.pointRole(new OriginRef.InvariantOrigin(rule, true),
                        BoundaryObligation.BoundarySide.AT));
        assertEquals(BoundaryObligation.PointRole.OFF,
                BoundaryObligation.pointRole(new OriginRef.InvariantOrigin(rule, false),
                        BoundaryObligation.BoundarySide.AT));
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

    /** Each line of the model's borders as {@code side/point}, in the order the report writes them. */
    private static List<String> sidesAndPoints(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        JsonNode root = JsonMapper.builder().build()
                .readTree(AdequacyReport.of(compilation).json(SourceNameResolver.identity()));
        List<String> out = new ArrayList<>();
        root.findValues("boundaries").forEach(each -> each.forEach(
                b -> out.add(b.get("side").asText() + "/" + b.get("point").asText())));
        return out;
    }

    private static String report(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).human(SourceNameResolver.identity());
    }
}
