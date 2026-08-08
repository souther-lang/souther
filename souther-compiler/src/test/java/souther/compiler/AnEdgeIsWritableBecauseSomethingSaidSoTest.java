package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BoundaryAssessment;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What says a row can be written at a boundary, and what a refusal is not.
 *
 * <p>Three things can say it and one thing cannot. A projection that read every rule of the value
 * proves it; a row already at the value witnesses it; a value built through the module's own decoder
 * witnesses it. The decoder refusing every candidate it tried says nothing — another value of the
 * same edge may build — so a refusal leaves the edge unknown and never closes it.
 *
 * <p>Held here rather than through the report, because the report prints only the two ends of this:
 * a line it counts and a line it says it cannot promise. Which of the three settled a line, and that
 * a refusal settled nothing, are the facts the counting is derived from, and a test that read them
 * off the printed line could not tell a witness from a proof.
 */
class AnEdgeIsWritableBecauseSomethingSaidSoTest {

    /**
     * Two edges of one range, one refused by a rule that reaches it and one not.
     *
     * <p>{@code value /= 0} is a rule the projection cannot take into a bound, so neither edge is
     * proven. It reaches the bottom of the range and nothing else: the decoder refuses a 0 and builds
     * a 10. The pair is the whole point — an answer that turned {@code allRulesRead == false} into
     * "writable" would settle both, and one that kept it as "not writable" would settle neither.
     */
    private static final String HOLED = """
            module example.holed

            data N = Int
                invariant within = value >= 0 && value <= 10
                invariant nonzero = value /= 0

            data Ok

            behavior f : (n: N) -> Ok
                constructs Ok

            let f (n) = Ok

            example f
                | "x" : (N(3)) -> Ok
            """;

    @Test
    void aRuleTheProjectionCouldNotReadLeavesTheEdgeItRefusesUnknown() {
        assertInstanceOf(BoundaryAssessment.Writability.Unknown.class,
                writabilityAt(HOLED, "example.holed", "f", "0"),
                "the decoder refused every candidate at 0");
        assertEquals(BoundaryAssessment.Writability.Unknown.Reason.REFUSED,
                ((BoundaryAssessment.Writability.Unknown)
                        writabilityAt(HOLED, "example.holed", "f", "0")).reason(),
                "and refused is not impossible: nothing here says no row can be written");
    }

    @Test
    void anEdgeTheSameRuleDoesNotReachIsWitnessedByTheValueThatWasBuilt() {
        assertInstanceOf(BoundaryAssessment.Writability.WitnessedByConstruction.class,
                writabilityAt(HOLED, "example.holed", "f", "10"),
                "a value at 10 went through the decoder");
    }

    /**
     * A rule about another position does not disqualify this one.
     *
     * <p>{@code String.matches} on the identifier is outside the fragment the projection reads, so
     * nothing about this value is proven — and it cannot refuse an amount whatever it does to an id.
     * Which is the shape most of a real model has: one clause somewhere in a record used to leave
     * every numeric edge in it unpromised.
     */
    @Test
    void anUnreadRuleOnAnotherFieldDoesNotLeaveThisEdgeUnknown() {
        String model = """
                module example.order

                data OrderId = String
                    invariant String.matches("[0-9]{4}", value)

                data Amount = Int
                    invariant value >= 0

                data Order = { id: OrderId, amount: Amount }

                data Ok

                behavior place : (order: Order) -> Ok
                    constructs Ok

                let place (order) = Ok

                example place
                    | "some" : (Order { id = OrderId("0001"), amount = Amount(7) }) -> Ok
                """;
        assertInstanceOf(BoundaryAssessment.Writability.WitnessedByConstruction.class,
                writabilityAt(model, "example.order", "place", "0"),
                "the id's rule cannot refuse an amount of 0");
    }

    /** A row at the value settles it, and nothing is built to find out what the row already shows. */
    @Test
    void aRowAtTheValueIsTheWitnessAndNothingIsBuilt() {
        String model = """
                module example.at

                data N = Int
                    invariant within = value >= 0 && value <= 10
                    invariant nonzero = value /= 3

                data Ok

                behavior f : (n: N) -> Ok
                    constructs Ok

                let f (n) = Ok

                example f
                    | "bottom" : (N(0)) -> Ok
                """;
        BoundaryAssessment at = assessmentAt(model, "example.at", "f", "0");
        assertInstanceOf(BoundaryAssessment.Coverage.Hit.class, at.coverage());
        assertInstanceOf(BoundaryAssessment.Writability.WitnessedByRow.class, at.writability(),
                "the row is the witness; no candidate was built for a value that is already there");
    }

    /**
     * A behavior no row names has no coverage answer and may still have a writability one.
     *
     * <p>Two observations on two axes, and the report used to print the second as though it were the
     * first — a behavior whose only problem was that nobody had written a row yet was reported under
     * "not known to be writable", beside a note saying the line was never measured.
     */
    @Test
    void aBehaviorNoRowNamesIsUnmeasuredAndNotUnwritable() {
        String model = """
                module example.unnamed

                data N = Int
                    invariant within = value >= 0 && value <= 10

                data Ok

                behavior f : (n: N) -> Ok
                    constructs Ok

                let f (n) = Ok

                data Other

                behavior g : (n: N) -> Other
                    constructs Other

                let g (n) = Other

                example g
                    | "some" : (N(4)) -> Other
                """;
        BoundaryAssessment at = assessmentAt(model, "example.unnamed", "f", "0");
        BoundaryAssessment.Coverage.NotMeasured absent = assertInstanceOf(
                BoundaryAssessment.Coverage.NotMeasured.class, at.coverage());
        assertEquals(BoundaryAssessment.Coverage.Reason.NO_ROWS, absent.reason());
        assertTrue(at.writability().known(),
                "nobody wrote a row, which says nothing about whether one could be written");
    }

    private static BoundaryAssessment.Writability writabilityAt(String model, String module,
                                                                String behavior, String value) {
        return assessmentAt(model, module, behavior, value).writability();
    }

    private static BoundaryAssessment assessmentAt(String model, String module, String behavior,
                                                   String value) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Map<String, List<BoundaryAssessment>> boundaries =
                compilation.db().ask(new Adequacy.Boundaries(module)).value();
        assertNotNull(boundaries, "the model under test compiles");
        return boundaries.get(behavior).stream().filter(b -> b.value().equals(value))
                .findFirst().orElseThrow(
                        () -> new AssertionError("no boundary at " + value + " of " + behavior));
    }
}
