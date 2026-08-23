package souther.compiler;

import souther.compiler.query.Measurement;
import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceNameResolver;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.ItemAssessment;
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
     * A clause placing an end at a value the clause beside it takes away.
     *
     * <p>{@code within} writes the bottom of the range at 0 and {@code nonzero} refuses the 0, and
     * the two are read by different readings: an end is placed by whichever clause states one, and a
     * denial states none. So the end as written is at 0 and the position starts at 1, and the line
     * this position has is the one at 1 — a line at 0 is a line at no value of {@code N}, and asking
     * whether a row can be written there asks about a value the model excludes.
     *
     * <p>Which rule the line belongs to does not move with it. {@code within} placed it and holds it
     * still; {@code nonzero} did not draw a new line at 1.
     */
    private static final String HOLED = """
            module example.holed

            data N = Int
                invariant within = value >= 0 && value <= 10
                invariant nonzero = value /= 0

            data Ok

            behavior f : (n: N) -> Ok

            let f (n) = Ok

            example f
                | "x" : (N(3)) -> Ok
            """;

    @Test
    void anEndTakenAwayByAClauseBesideItIsALineAtTheValueTheRulesLeave() {
        assertEquals(List.of("1", "10"), valuesAt(HOLED, "example.holed", "f"),
                "the position starts at 1, so that is where the line is and 0 is no line of it");

        ItemAssessment.Owed at = assessmentAt(HOLED, "example.holed", "f", "1");
        assertInstanceOf(ItemAssessment.Writability.WitnessedByConstruction.class,
                at.writability(),
                "and a value at it went through the decoder, which is more than a proof of one");
    }

    @Test
    void anEdgeTheSameRuleDoesNotReachIsWitnessedByTheValueThatWasBuilt() {
        ItemAssessment.Owed at = assessmentAt(HOLED, "example.holed", "f", "10");

        assertInstanceOf(ItemAssessment.Writability.WitnessedByConstruction.class,
                at.writability(), "a value at 10 went through the decoder");
        assertInstanceOf(ItemAssessment.Attempt.Built.class, at.attempt(),
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

            let place (amount, code) = Ok

            example place
                | "some" : (Amount(7), Code("ab")) -> Ok
            """;

    @Test
    void anEdgeTheProjectionProvesCanStillBeOneNoSearchReached() {
        ItemAssessment.Owed at =
                assessmentAt(PROVEN_BUT_UNREACHED, "example.proven", "place", "0");

        assertInstanceOf(ItemAssessment.Coverage.NoHit.class,
at.coverage().made().orElseThrow());
        assertInstanceOf(ItemAssessment.Writability.ProvenByProjection.class, at.writability(),
                "every rule of `Amount` was read, so 0 is a value it holds");
        assertInstanceOf(ItemAssessment.Attempt.Unresolved.class, at.attempt(),
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
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        String block = souther.compiler.report.GeneratedRows.of(
                compilation, "example.proven", "place", true, SourceNameResolver.identity()).text();

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

                let place (order) = Ok

                example place
                    | "some" : (Order { id = OrderId("0001"), amount = Amount(7) }) -> Ok
                """;
        assertInstanceOf(ItemAssessment.Writability.WitnessedByConstruction.class,
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

                let f (n) = Ok

                example f
                    | "bottom" : (N(0)) -> Ok
                """;
        ItemAssessment.Owed at = assessmentAt(model, "example.at", "f", "0");
        assertInstanceOf(ItemAssessment.Coverage.Hit.class,
at.coverage().made().orElseThrow());
        assertInstanceOf(ItemAssessment.Writability.WitnessedByRow.class, at.writability(),
                "the row is the witness");
        assertEquals(ItemAssessment.Attempt.Reason.A_ROW_IS_ALREADY_THERE,
                assertInstanceOf(ItemAssessment.Attempt.NotAttempted.class, at.attempt())
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

                let f (n) = Ok

                data Other

                behavior g : (n: N) -> Other

                let g (n) = Other

                example g
                    | "some" : (N(4)) -> Other
                """;
        ItemAssessment.Owed at = assessmentAt(model, "example.unnamed", "f", "0");
        assertEquals(ItemAssessment.Coverage.NotAsked.NO_ROWS,
                assertInstanceOf(Measurement.NotMeasured.class, at.coverage()).why());
        assertTrue(at.writability().known(),
                "nobody wrote a row, which says nothing about whether one could be written");
        assertInstanceOf(ItemAssessment.Attempt.Built.class, at.attempt(),
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

                let f (n) = if n.value <= 4 then Ok else Big

                example f
                    | "some" : (N(2)) -> Ok
                """;
        Compilation compilation = Compilation.ofSource(model, "Main");
        // What a guard's line waits on, and this build does not ask for it.
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.WITNESS));
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> boundaries =
                compilation.db().ask(new Adequacy.Boundaries("example.waiting")).value();

        List<BorderAssessment.Point> guards =
                BorderAssessment.pointsOf(boundaries.get("f")).stream()
                        .filter(p -> p.border().rule().isWrittenRatherThanNamed())
                        .filter(p -> p.owed() != null).toList();
        assertFalse(guards.isEmpty(), "the comparison draws lines: " + boundaries.get("f"));
        for (BorderAssessment.Point at : guards) {
            assertEquals(ItemAssessment.Coverage.NotAsked.ARMS_NOT_ASKED,
                    assertInstanceOf(Measurement.NotMeasured.class,
                            at.owed().coverage()).why(), at.label());
            assertEquals(ItemAssessment.Attempt.Reason.NOT_MEASURED,
                    assertInstanceOf(ItemAssessment.Attempt.NotAttempted.class,
                            at.owed().attempt()).reason(), at.label());
        }
    }

    /** Every value a point against a line names, as the report names them. */
    private static List<String> valuesAt(String model, String module, String behavior) {
        return pointsAt(model, module, behavior).stream()
                .filter(p -> p.role().againstTheLine()).filter(p -> p.owed() != null)
                .map(BorderAssessment.Point::against).sorted().toList();
    }

    private static ItemAssessment.Writability writabilityAt(String model, String module,
                                                                String behavior, String value) {
        return assessmentAt(model, module, behavior, value).writability();
    }

    /** The point against a line at {@code value}, which is what a row there is owed for. */
    private static ItemAssessment.Owed assessmentAt(String model, String module, String behavior,
                                                    String value) {
        return assessmentAt(model, module, behavior, value, Adequacy.Level.ALL);
    }

    private static ItemAssessment.Owed assessmentAt(String model, String module, String behavior,
                                                    String value, Adequacy.Level level) {
        return pointsAt(model, module, behavior, level).stream()
                .filter(p -> p.role().againstTheLine()).filter(p -> p.owed() != null)
                .filter(p -> value.equals(p.against()))
                .findFirst().map(BorderAssessment.Point::owed).orElseThrow(
                        () -> new AssertionError("no boundary at " + value + " of " + behavior));
    }

    /**
     * A level that composes no value falls back on what the rules prove, and says why it built none.
     *
     * <p>Composing a candidate costs a decoder run for each point it settles — sixteen seconds over
     * the corpus this was measured on, against a second for everything else a build at
     * {@code witness} does. That is not reading what the rows already established, so it is not what
     * the level promises, and it composes none (issue #955).
     *
     * <p>What it does not cost is the answer. Nothing a search does can take a proof away, so an
     * edge inside what every rule reaching it leaves is writable because the rules say so, whichever
     * level asked — and the row that is owed there is owed at both. What a composed value adds is a
     * witness for the edges the rules cannot reach, and what a person is offered to paste.
     *
     * <p>And the two nothings are told apart. Read off the same field, an edge nobody tried to build
     * at and an edge every value tried at was refused are one answer, and only the first is this
     * build's doing.
     */
    @Test
    void aLevelThatComposesNoValueStillReadsWhatTheRulesProve() {
        ItemAssessment.Owed built = assessmentAt(HOLED, "example.holed", "f", "1");
        assertInstanceOf(ItemAssessment.Writability.WitnessedByConstruction.class,
                built.writability(), "at `all` a value at it went through the decoder");

        ItemAssessment.Owed unbuilt = assessmentAt(HOLED, "example.holed", "f", "1",
                Adequacy.Level.WITNESS);
        assertInstanceOf(ItemAssessment.Writability.ProvenByProjection.class,
                unbuilt.writability(), "and the rules prove it whether or not anything was built");
        assertEquals(ItemAssessment.Attempt.Reason.VALUES_NOT_ASKED_FOR,
                assertInstanceOf(ItemAssessment.Attempt.NotAttempted.class, unbuilt.attempt())
                        .reason(),
                "said as this build's doing and not as a refusal");
        assertInstanceOf(Measurement.Complete.class, unbuilt.coverage(),
                "the rows were read all the same: what is missing is the value, not the reading");
        assertTrue(unbuilt.coverage().made().orElseThrow() instanceof ItemAssessment.Coverage.NoHit
                        && unbuilt.writability().known(),
                "so the row is owed at both levels, and this one offers no value to write there");
    }

    private static List<BorderAssessment.Point> pointsAt(String model, String module,
                                                         String behavior) {
        return pointsAt(model, module, behavior, Adequacy.Level.ALL);
    }

    private static List<BorderAssessment.Point> pointsAt(String model, String module,
                                                         String behavior, Adequacy.Level level) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(level));
        compilation.answerEverything();
        Map<String, List<BorderAssessment>> boundaries =
                compilation.db().ask(new Adequacy.Boundaries(module)).value();
        assertNotNull(boundaries, "the model under test compiles");
        return BorderAssessment.pointsOf(boundaries.get(behavior));
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
            let onADate (c) = Ok

            behavior onAMoment : (m: Moment) -> Ok
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
            ItemAssessment.Owed at = assessmentAt(TEMPORAL_EDGE_NOTHING_COMPOSED,
                    "example.temporal", each[0], each[1].substring(each[1].indexOf('=') + 2));

            assertInstanceOf(ItemAssessment.Attempt.Unresolved.class, at.attempt(),
                    each[0] + ": the search came back with nothing");

            Compilation compilation =
                    Compilation.ofSource(TEMPORAL_EDGE_NOTHING_COMPOSED, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            String block = souther.compiler.report.GeneratedRows.of(
                    compilation, "example.temporal", each[0], true, SourceNameResolver.identity()).text();

            assertTrue(block.contains("no row for `" + each[1] + "`"), block);
            assertTrue(block.contains("does not make the combination impossible"), block);
            assertFalse(block.contains("not derivable"),
                    "the rule that drew the line is two lines above: " + block);
        }
    }
}
