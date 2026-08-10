package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.Generator;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BoundaryAssessment;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
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
        BoundaryAssessment at = assessmentAt(HOLED, "example.holed", "f", "0");

        assertInstanceOf(BoundaryAssessment.Writability.Unknown.class, at.writability(),
                "nothing proved it and nothing built it");
        BoundaryAssessment.Attempt.Unresolved unresolved = assertInstanceOf(
                BoundaryAssessment.Attempt.Unresolved.class, at.attempt(),
                "and refused is not impossible: nothing here says no row can be written");
        assertEquals(Generator.UnresolvedCombination.Reason.ALL_CANDIDATES_REJECTED,
                unresolved.why().reason());
    }

    @Test
    void anEdgeTheSameRuleDoesNotReachIsWitnessedByTheValueThatWasBuilt() {
        BoundaryAssessment at = assessmentAt(HOLED, "example.holed", "f", "10");

        assertInstanceOf(BoundaryAssessment.Writability.WitnessedByConstruction.class,
                at.writability(), "a value at 10 went through the decoder");
        assertInstanceOf(BoundaryAssessment.Attempt.Built.class, at.attempt(),
                "and the value it built is kept, because it is also the row an author is offered");
    }

    /**
     * A projection's proof and a search that came back with nothing are both true at once.
     *
     * <p>Two answers about two different things: whether a value at the edge exists, and whether this
     * run managed to produce one. Reading the second off the first is what left `--generate` silent
     * about a boundary it could say something useful about — the report named the row as owed and the
     * block printed neither a row nor a reason.
     *
     * <p>Every rule of {@code Amount} was read, so 0 is proven to be a value it holds. The row needs a
     * second input as well, and nothing can be written for that one — which is a fact about this
     * search and not about the edge.
     */
    private static final String PROVEN_BUT_UNREACHED = """
            module example.proven

            data Amount = Int
                invariant value >= 0

            data Code = String
                invariant String.matches("(?=.*a).*b", value)

            data Ok

            behavior place : (amount: Amount, code: Code) -> Ok
                constructs Ok

            let place (amount, code) = Ok

            example place
                | "some" : (Amount(7), Code("ab")) -> Ok
            """;

    @Test
    void anEdgeTheProjectionProvesCanStillBeOneNoSearchReached() {
        BoundaryAssessment at =
                assessmentAt(PROVEN_BUT_UNREACHED, "example.proven", "place", "0");

        assertInstanceOf(BoundaryAssessment.Coverage.Missed.class, at.coverage());
        assertInstanceOf(BoundaryAssessment.Writability.ProvenByProjection.class, at.writability(),
                "every rule of `Amount` was read, so 0 is a value it holds");
        assertInstanceOf(BoundaryAssessment.Attempt.Unresolved.class, at.attempt(),
                "and the search still came back with nothing, which takes nothing away from that");
    }

    /**
     * The same boundary, as the block an author reads.
     *
     * <p>This is what recovering the attempt from the verdict cost: the report named the row as owed
     * and the block said nothing at all, because the verdict was "provable" and the attempt that had
     * failed was no longer anywhere to be read.
     */
    @Test
    void anEdgeNoSearchReachedIsStillSaidInTheBlock() {
        Compilation compilation = Compilation.ofSource(PROVEN_BUT_UNREACHED, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();

        String block = souther.compiler.report.GeneratedRows.of(
                compilation, "example.proven", "place", true);

        assertTrue(block.contains("no row for `amount = 0` in `place`"), block);
        assertTrue(block.contains("every value tried was refused"), block);
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
                "the row is the witness");
        assertEquals(BoundaryAssessment.Attempt.Reason.A_ROW_IS_ALREADY_THERE,
                assertInstanceOf(BoundaryAssessment.Attempt.NotAttempted.class, at.attempt())
                        .reason(),
                "and no candidate was built for a value that is already there");
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
        assertInstanceOf(BoundaryAssessment.Attempt.Built.class, at.attempt(),
                "a value was built here, and what it settles is the writability and not the rows");
    }

    /**
     * A line waiting on the arms is a line nothing is built for.
     *
     * <p>Meeting a guard's line takes the comparison having run, which nothing measures until the
     * build asks for the arms. Until then no row there is owed to anybody, and building a candidate
     * would hand somebody a specific piece of work on the strength of a question nobody put.
     */
    @Test
    void aLineWaitingOnTheArmsIsALineNothingIsBuiltFor() {
        String model = """
                module example.waiting

                data N = Int
                    invariant within = value >= 0 && value <= 10

                data Ok
                data Big

                behavior f : (n: N) -> Ok | Big
                    constructs Ok, Big

                let f (n) = if n.value <= 4 then Ok else Big

                example f
                    | "some" : (N(2)) -> Ok
                """;
        Compilation compilation = Compilation.ofSource(model, "Main");
        // What a guard's line waits on, and this build does not ask for it.
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        compilation.answerEverything();
        Map<String, List<BoundaryAssessment>> boundaries =
                compilation.db().ask(new Adequacy.Boundaries("example.waiting")).value();

        List<BoundaryAssessment> guards = boundaries.get("f").stream()
                .filter(b -> b.origin().startsWith("guard")).toList();
        assertFalse(guards.isEmpty(), "the comparison draws lines: " + boundaries.get("f"));
        for (BoundaryAssessment at : guards) {
            assertEquals(BoundaryAssessment.Coverage.Reason.ARMS_NOT_ASKED,
                    assertInstanceOf(BoundaryAssessment.Coverage.NotMeasured.class, at.coverage())
                            .reason(), at.label());
            assertEquals(BoundaryAssessment.Attempt.Reason.NOT_MEASURED,
                    assertInstanceOf(BoundaryAssessment.Attempt.NotAttempted.class, at.attempt())
                            .reason(), at.label());
        }
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

    /**
     * A line on a temporal, which nothing could compose a row at.
     *
     * <p>The same two answers on the carriers the numbers above do not cover. A rule this reads
     * bounds the value and a rule beside it refuses the value at that bound, so the line exists and
     * the row does not — and which of the two failed decides what an author is told to do about it.
     * Read here on both temporal carriers, because they reach the generator by different writers and
     * a count written where a temporal belongs is refused by the decoder with nothing said about why.
     */
    private static final String TEMPORAL_EDGE_NOTHING_COMPOSED = """
            module example.temporal

            data Cutoff = Date
                invariant value >= Date("2026-01-01") && value /= Date("2026-01-01")
            data Moment = DateTime
                invariant value >= DateTime("2026-01-01T00:00:00")
                    && value /= DateTime("2026-01-01T00:00:00")

            data Ok

            behavior onADate : (c: Cutoff) -> Ok
                constructs Ok
            let onADate (c) = Ok

            behavior onAMoment : (m: Moment) -> Ok
                constructs Ok
            let onAMoment (m) = Ok

            example onADate
                | "some" : (Cutoff(Date("2026-06-01"))) -> Ok

            example onAMoment
                | "some" : (Moment(DateTime("2026-06-01T00:00:00"))) -> Ok
            """;

    @Test
    void aTemporalEdgeNothingComposedIsTheSearchsFailureAndNotTheModelsSilence() {
        for (String[] each : new String[][] {
                {"onADate", "c = 2026-01-01"}, {"onAMoment", "m = 2026-01-01T00:00:00"}}) {
            BoundaryAssessment at = assessmentAt(TEMPORAL_EDGE_NOTHING_COMPOSED,
                    "example.temporal", each[0], each[1].substring(each[1].indexOf('=') + 2));

            assertInstanceOf(BoundaryAssessment.Attempt.Unresolved.class, at.attempt(),
                    each[0] + ": the search came back with nothing");

            Compilation compilation =
                    Compilation.ofSource(TEMPORAL_EDGE_NOTHING_COMPOSED, "Main");
            compilation.measure(Adequacy.Asked.reportOnly());
            compilation.answerEverything();
            String block = souther.compiler.report.GeneratedRows.of(
                    compilation, "example.temporal", each[0], true);

            assertTrue(block.contains("no row for `" + each[1] + "`"), block);
            assertTrue(block.contains("does not make the combination impossible"), block);
            assertFalse(block.contains("not derivable"),
                    "the rule that drew the line is two lines above: " + block);
        }
    }
}
