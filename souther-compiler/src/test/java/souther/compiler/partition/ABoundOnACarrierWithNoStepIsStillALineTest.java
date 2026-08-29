package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.ItemAssessment;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A bound is a line wherever the rule stops, and the value a row is written at is asked of the order
 * afterwards.
 *
 * <p>The two used to be one. A strict bound is finished by moving the end onto a value the position
 * holds — {@code value > 5} on an {@code Int} arrives as an inclusive 6 — and every reader after that
 * took the cut for the point. A carrier with no step has no such move, so {@code value > 5.0m}
 * arrives as an exclusive 5, which is a value the position does not hold; the line was then dropped
 * for having no point on it, and the measure came back saying the rules of the behavior draw no line
 * anywhere.
 *
 * <p>Both carriers are here and they differ in one thing. A model whose every rule is a bound on a
 * {@code Decimal} was reported adequate on the strength of no measure at all (issue #1079), and an
 * expectation written against the decimal alone holds against a reader that draws no line on either.
 */
class ABoundOnACarrierWithNoStepIsStillALineTest {

    /** One field bounded strictly away from zero, on whichever carrier is asked for. */
    private static String model(String carrier, String bound) {
        return """
                module example.step

                data Positive = %s
                    invariant positive = value > %s

                data Holder = { p: Positive }

                data Ok

                behavior take : (h: Holder) -> Ok
                let take (h) = Ok
                """.formatted(carrier, bound);
    }

    /**
     * The line is where the rule stops, on both carriers, and it is one line either way.
     *
     * <p>Where the rule stops is what the author wrote. A step onto the next value is how a discrete
     * carrier says the same thing, and the line an {@code Int} draws at 1 and the line a
     * {@code Decimal} draws at 0 are one rule's line read on two orders.
     */
    @Test
    void aStrictBoundDrawsALineOnEitherCarrier() {
        assertEquals(List.of("h.p = 0"), labels(model("Decimal", "0m")),
                "`value > 0m` stops the position at zero");
        assertEquals(List.of("h.p = 1"), labels(model("Int", "0")),
                "`value > 0` on a whole number stops it at the one it leaves");
    }

    /**
     * The point against the line is the carrier's answer, and the two carriers answer differently.
     *
     * <p>An {@code Int} has a least admitted value and a row can be written at it. A {@code Decimal}
     * has none — every value above zero has one below it that is also above zero — so the point the
     * technique asks for cannot be written down, which is a limit of the language and not a row
     * anybody is short of.
     */
    @Test
    void theOnPointIsOwedWhereTheCarrierNamesItAndNotWhereItDoesNot() {
        assertEquals(new ItemAssessment.NotOwed(NotOwedReason.THE_CARRIER_NAMES_NO_NEIGHBOUR),
                border(model("Decimal", "0m")).at(PointRole.ON),
                "no decimal is the least one above zero");
        assertInstanceOf(ItemAssessment.Owed.class, border(model("Int", "0")).at(PointRole.ON),
                "one is the least whole number above zero, and a row can be written there");
    }

    /**
     * Nothing outside a bound can be constructed, whichever carrier it is on.
     *
     * <p>Which is what tells this from the point above. The far side holds no value because the
     * model refuses it, and the point against the line on the near side is missing because the order
     * has no name for it — a reader told the second where the first is true would go looking for a
     * conversion, and one told the first where the second is true would think the rules had
     * discharged something.
     */
    @Test
    void aBoundOwesNothingOutsideItselfOnEitherCarrier() {
        for (String carrier : List.of("Decimal", "Int")) {
            BorderAssessment line = border(model(carrier, carrier.equals("Decimal") ? "0m" : "0"));
            assertEquals(new ItemAssessment.NotOwed(NotOwedReason.THE_RULES_REFUSE_IT),
                    line.at(PointRole.OFF), carrier + ": nothing is just outside a bound");
            assertEquals(new ItemAssessment.NotOwed(NotOwedReason.THE_RULES_REFUSE_IT),
                    line.at(PointRole.OUT), carrier + ": nothing is outside a bound at all");
        }
    }

    /**
     * And the side the bound keeps is owed a row on both.
     *
     * <p>The whole of what the measure gains here. A {@code Decimal} above zero is a value anybody
     * can write, so the model owes a row for it — and while the line was dropped the behavior was
     * reported adequate without one.
     */
    @Test
    void theSideTheBoundKeepsIsOwedARowOnEitherCarrier() {
        assertInstanceOf(ItemAssessment.Owed.class, border(model("Decimal", "0m")).at(PointRole.IN),
                "some decimal is above zero");
        assertInstanceOf(ItemAssessment.Owed.class, border(model("Int", "0")).at(PointRole.IN),
                "some whole number is above zero");
    }

    /** The one line this model draws. */
    private static BorderAssessment border(String model) {
        List<BorderAssessment> lines = bordersOf(model);
        assertEquals(1, lines.size(), () -> "one rule, one line: " + labelsOf(lines));
        return lines.getFirst();
    }

    private static List<String> labels(String model) {
        return labelsOf(bordersOf(model));
    }

    private static List<String> labelsOf(List<BorderAssessment> lines) {
        return lines.stream().map(BorderAssessment::label).toList();
    }

    private static List<BorderAssessment> bordersOf(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> boundaries =
                Adequacy.boundariesOf(compilation.db(), "example.step");
        assertNotNull(boundaries, "the model under test compiles");
        return boundaries.values().stream().flatMap(List::stream).toList();
    }
}
