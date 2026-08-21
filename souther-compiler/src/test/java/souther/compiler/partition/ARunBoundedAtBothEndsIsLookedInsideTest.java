package souther.compiler.partition;

import souther.compiler.numeric.Towards;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.Count;
import souther.compiler.numeric.Text;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A run between two lines is looked inside, at whatever the quantity has there.
 *
 * <p>What the order takes and what a search could name used to be two answers, and on an order whose
 * values fill they disagreed: {@code 3 * n} over decimals reaches every third of one, and the only
 * levels anything offered were the whole multiples of three. A run between one and two holds
 * infinitely many of the first and none of the second, so the point inside it was reported as one
 * the search stopped before reaching — with no search having run at all (issue #903).
 *
 * <p>Measured against a run three times as wide, which differs in one thing: whether a whole multiple
 * of the generator happens to fall inside it. That one already worked, and an expectation on it alone
 * holds against the reading that lost the narrow one.
 */
class ARunBoundedAtBothEndsIsLookedInsideTest {

    /** One decimal, cut twice on a multiple of itself, leaving a run between the two lines. */
    private static String cut(String upper) {
        return """
                module example.form

                data No = { why: Int }
                data Yes = { v: Int }
                data Result = No | Yes

                behavior f : (n: Decimal) -> Result
                    constructs Yes, No

                let f (n) = {
                    guard 3m * n > 1m else No { why = 0 }
                    guard 3m * n > %sm else No { why = 1 }
                    Yes { v = 1 }
                }

                example f
                    | "one" : (0m) -> No { why = 0 }
                """.formatted(upper);
    }

    /**
     * A run narrower than the step anything used to take is offered a row, and so is a wide one.
     *
     * <p>The pair is the measurement. Both runs lie between two lines on the same quantity and hold
     * the same kind of value; they differ in whether three — the first level the old walk could name
     * — is inside. Held on the wide one alone, every reading of this passes.
     */
    @Test
    void aRunHoldingNoWholeMultipleOfTheGeneratorIsStillLookedIn() {
        assertEquals(souther.compiler.query.ItemAssessment.Attempt.Built.class,
                attemptAt(cut("10"), "3 * n = 1", PointRole.IN).getClass(),
                "a run from one to ten holds three, which anything could name");
        assertEquals(souther.compiler.query.ItemAssessment.Attempt.Built.class,
                attemptAt(cut("2"), "3 * n = 1", PointRole.IN).getClass(),
                "and one from one to two holds 1.5, which only looking inside it finds");
    }

    /**
     * The row offered for the point covers it once it is pasted back.
     *
     * <p>What a point asks of a row and what a search composes to stand for it are two answers, and
     * holding only the first let a row be offered that leaves the item where it was. Read as the
     * point's own verdict rather than as the text of the block, so that a row that happens to read
     * like another one is not mistaken for this one.
     */
    @Test
    void theRowOfferedForTheRunCoversItWhenItIsPastedBack() {
        String offered = rowAt(cut("2"), "3 * n = 1", PointRole.IN);
        assertNotNull(offered, "the narrow run is offered a row");

        BorderAssessment after = bordersOf(cut("2") + "    | \"inside\" : (" + offered
                + ") -> No { why = 1 }\n").get("3 * n = 1");
        assertNotNull(after);
        assertTrue(after.owedAt(PointRole.IN).coverage().hit(),
                "the row offered for the run is a row inside it: " + offered);
    }

    /**
     * What an order has in a run and what this can write down there are two answers, and all of
     * their combinations mean something.
     *
     * <p>Held as one, the third of them reads like the first and a coverage item goes away. Each is
     * measured on the order that produces it rather than on one order asked four ways, because which
     * of the four a run falls into is exactly what the order decides.
     */
    @Test
    void whatARunHoldsAndWhatCanBeWrittenInItAreToldApart() {
        LevelInterval between = new LevelInterval(
                Bound.at(count(1), false), Bound.at(count(2), false));

        LevelSpace fills = LevelSpace.overFiniteDecimals(BigDecimal.valueOf(3));
        assertInstanceOf(Occupancy.Inhabited.class, fills.inspect(between),
                "three times a decimal reaches every third of one, so it reaches into this run");
        Level found = assertInstanceOf(Witness.Found.class,
                fills.witness(between, Towards.ABOVE)).level();
        assertTrue(fills.attainable(found) && between.contains(found),
                "and what comes back is a value it takes, inside the run: " + found);

        LevelSpace steps = LevelSpace.steppingBy(BigDecimal.valueOf(3));
        assertEquals(new Occupancy.Empty(), steps.inspect(between),
                "counting by threes there is nothing between one and two at all");
        assertEquals(Witness.NONE, steps.witness(between, Towards.ABOVE),
                "so nothing is written there either");
    }

    /**
     * A run this will not name a value in is not a run with nothing in it.
     *
     * <p>The combination the other three would hide. Every string with {@code b} as a prefix is above
     * it, so the run is inhabited; which one to write is a choice, and a choice made in the compiler
     * puts a character nobody wrote into a row somebody has to read.
     */
    @Test
    void aRunThisDeclinesToNameAValueInIsStillInhabited() {
        LevelSpace strings = LevelSpace.onACarrier(souther.compiler.check.Carrier.TEXT);
        LevelInterval above = new LevelInterval(
                Bound.at(new Level.OnACarrier(souther.compiler.check.Carrier.TEXT, Text.of("b")),
                        false), null);

        assertInstanceOf(Occupancy.Inhabited.class, strings.inspect(above));
        assertEquals(Witness.NONE, strings.witness(above, Towards.ABOVE));
    }

    private static Level count(long at) {
        return new Level.ACount(Count.of(at));
    }

    /** What was tried at one point of one border. */
    private static souther.compiler.query.ItemAssessment.Attempt attemptAt(
            String model, String border, PointRole role) {
        BorderAssessment at = bordersOf(model).get(border);
        assertNotNull(at, bordersOf(model).keySet().toString());
        return at.owedAt(role).attempt();
    }

    /** The row offered at one point, as a reader would paste it, or null where none was. */
    private static String rowAt(String model, String border, PointRole role) {
        return attemptAt(model, border, role)
                instanceof souther.compiler.query.ItemAssessment.Attempt.Built built
                ? built.row().inputs().stream().map(FixtureTemplate::text)
                        .collect(java.util.stream.Collectors.joining(", "))
                : null;
    }

    private static Map<String, BorderAssessment> bordersOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> boundaries =
                compilation.db().ask(new Adequacy.Boundaries("example.form")).value();
        assertNotNull(boundaries, "the model under test compiles");
        Map<String, BorderAssessment> out = new java.util.LinkedHashMap<>();
        boundaries.values().forEach(each -> each.forEach(b -> out.put(b.label(), b)));
        return out;
    }

}
