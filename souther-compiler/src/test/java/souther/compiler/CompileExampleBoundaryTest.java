package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Which classes and which boundaries a behavior's rows actually reach.
 *
 * <p>The two are measured differently on purpose. Being in a class is a property of the value a row
 * wrote. Meeting a boundary a {@code guard} drew is not: the comparison has to have been evaluated,
 * and a row can carry the exact value and never reach the guard, so until the arms are instrumented
 * those boundaries are reported as not measured rather than as met or missed.
 */
class CompileExampleBoundaryTest {

    private static final String MODEL = """
            module example.trip

            data Amount = Int
                invariant value >= 0

            data Draft = { cost: Amount }
            data Submitted = { cost: Amount }
            data Waiting = { cost: Amount }

            behavior submit : (request: Draft) -> Submitted | Waiting
                constructs Submitted, Waiting

            let submit (request) = {
                guard request.cost.value <= 100 else Waiting { cost = request.cost }
                Submitted { cost = request.cost }
            }
            """;

    private static PartitionEvidence evidence(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        Map<String, PartitionEvidence> all = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        assertNotNull(all, "the model under test compiles");
        return all.get("submit");
    }

    private static PartitionEvidence.AxisCoverage cost(PartitionEvidence evidence) {
        return evidence.axes().stream().filter(a -> a.path().equals("request.cost"))
                .findFirst().orElseThrow();
    }

    private static List<PartitionEvidence.BoundaryCoverage> at(PartitionEvidence evidence,
                                                               String value) {
        return evidence.boundaries().stream().filter(b -> b.value().equals(value)).toList();
    }

    @Test
    void aClassNoRowIsInIsReportedAsUncovered() {
        PartitionEvidence one = evidence(MODEL + """

                example submit
                    | (Draft { cost = Amount(50) }) -> Submitted
                """);

        assertEquals(List.of("request.cost/100 < x"), cost(one).uncovered());
        assertEquals(MeasurementStatus.COMPLETE, cost(one).status());

        PartitionEvidence both = evidence(MODEL + """

                example submit
                    | (Draft { cost = Amount(50) })  -> Submitted
                    | (Draft { cost = Amount(500) }) -> Waiting
                """);
        assertEquals(List.of(), cost(both).uncovered());
    }

    /** Nothing below the bound can be constructed, so writing the value is the whole of what there
     * is to reach — and reaching it needs no branch to have run. */
    @Test
    void anInvariantsBoundIsMetByWritingTheValue() {
        PartitionEvidence away = evidence(MODEL + """

                example submit
                    | (Draft { cost = Amount(50) }) -> Submitted
                """);
        PartitionEvidence.BoundaryCoverage zero = at(away, "0").get(0);
        assertFalse(zero.hit());
        assertEquals(MeasurementStatus.COMPLETE, zero.status());
        assertTrue(zero.origin().startsWith("invariant"), zero.origin());

        PartitionEvidence edge = evidence(MODEL + """

                example submit
                    | (Draft { cost = Amount(0) }) -> Submitted
                """);
        assertTrue(at(edge, "0").get(0).hit(), "a row is written at the edge");
    }

    @Test
    void aGuardsBoundaryIsNotMeasuredUntilTheArmsAre() {
        PartitionEvidence evidence = evidence(MODEL + """

                example submit
                    | (Draft { cost = Amount(100) }) -> Submitted
                """);

        PartitionEvidence.BoundaryCoverage hundred = at(evidence, "100").get(0);
        assertEquals(MeasurementStatus.UNAVAILABLE, hundred.status(),
                "the value is written, and whether the comparison ran is not yet known");
        assertFalse(hundred.hit(), "unavailable is not met");
        assertTrue(hundred.origin().startsWith("guard"), hundred.origin());
    }

    @Test
    void bothSidesOfAGuardsLineAreAskedFor() {
        PartitionEvidence evidence = evidence(MODEL + """

                example submit
                    | (Draft { cost = Amount(50) }) -> Submitted
                """);

        assertEquals(1, at(evidence, "100").size(), "the value itself");
        assertEquals(1, at(evidence, "101").size(), "and the first value on the other side");
    }

    /** Not a gap. The model draws no line through a plain String, so there was nothing to measure,
     * and saying so is different from reporting nothing covered. */
    @Test
    void aPositionTheModelDoesNotDivideIsNamedRatherThanCounted() {
        Compilation compilation = Compilation.ofSource("""
                module example.note

                data Note = String
                data Kept = { note: Note }

                behavior keep : (note: Note) -> Kept
                    constructs Kept

                let keep (note) = Kept { note = note }

                example keep
                    | (Note("x")) -> Kept { note = Note("x") }
                """, "Main");
        compilation.answerEverything();
        Map<String, PartitionEvidence> all = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        assertNotNull(all);
        PartitionEvidence keep = all.get("keep");

        assertEquals(List.of("note"), keep.notDerivable());
        assertEquals(List.of(), keep.axes());
        assertEquals(List.of(), keep.boundaries());
    }
}
