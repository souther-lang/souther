package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.report.AdequacyReport;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a measure could not read is not a fact about what the model says.
 *
 * <p>{@code NotApplicable} is the strongest thing a measure says: the model was read to the end and
 * holds no subject for this measure, so no row anybody writes would give it one. A measure that
 * introduces one from an empty collection is making that claim without the reading behind it — and
 * an empty collection is what a derivation that did not come back leaves.
 *
 * <p>The arm measure did it twice over. Which behaviors have a body was read off the elaborated
 * bodies and what each owes was read off the plan, which is itself read off them; a module the
 * compile stopped in has neither, so every behavior in it was answered "this behavior has no body"
 * — on a report whose line above said {@code implemented} (issue #996).
 *
 * <p>What holds the fix is that both directions are here. A derivation that is absent must not
 * produce an inapplicable answer, and a model that genuinely has no subject must still get one:
 * the correction is worthless if it turns every settled nothing into a doubt.
 */
class AnAbsentDerivationIsNotAProofAboutTheModelTest {

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static Adequacy.BranchEvidence branchOf(Compilation compilation, String module,
                                                    String behavior) {
        Map<String, Adequacy.BranchEvidence> branches =
                compilation.db().ask(new Adequacy.BranchCoverage(module)).value();
        assertNotNull(branches, "the arm measure answered for " + module);
        Adequacy.BranchEvidence branch = branches.get(behavior);
        assertNotNull(branch, "the arm measure answered for " + behavior);
        return branch;
    }

    /**
     * A model whose compile stops before the bodies are elaborated, with a {@code let} written.
     *
     * <p>The error is the point and not the subject: what this model has to be is one whose
     * declarations say a body is written and whose {@code Bodies.Checked} does not come back, and
     * the test asserts both rather than trusting the model to still arrange it.
     */
    private static final String STOPPED = """
            module example.rooms

            data Item = { sku: String }
            data Line = { sku: String }

            behavior pick : (item: Item) -> Line
                constructs Line
                ensures Line -> value.sku == item.sku
            let pick (item) = Line { sku = item.sku }

            example pick
                | "one" : (Item { sku = "a" }) -> Line { sku = "a" }
            """;

    /** A body that was not elaborated is a measurement that could not be finished. */
    @Test
    void aBodyThatWasNotElaboratedIsNotABehaviorWithNoBody() {
        Compilation compilation = measured(STOPPED);

        assertFalse(compilation.errors().isEmpty(), "this model is one the compile stops in");
        assertNull(compilation.db().ask(new Bodies.Checked("example.rooms")).value(),
                "and stops before the bodies are elaborated, which is what this is about");

        Measure<Adequacy.BranchEvidence.Arms> measured =
                branchOf(compilation, "example.rooms", "pick").measured();

        Measurement.FailedToMeasure<?> failed = assertInstanceOf(
                Measurement.FailedToMeasure.class, measured,
                () -> "the model says a body is written, so what it owes is unknown rather than"
                        + " nothing: " + measured);
        assertEquals(Adequacy.BranchEvidence.Unelaborated.BODIES_NOT_ELABORATED, failed.why());
        assertEquals(WeakeningSet.of(new Weakening.BodiesNotElaborated("example.rooms")),
                failed.by(), "and says what it went without");
    }

    /**
     * And the report does not say both things about it.
     *
     * <p>The two halves are a line apart. Read from the declarations the behavior is
     * {@code implemented}; read from the elaborated bodies it had none — and the report printed
     * each of them under the other.
     */
    @Test
    void theReportDoesNotCallAnImplementedBehaviorOneWithNoBody() {
        AdequacyReport report = AdequacyReport.of(measured(STOPPED));
        String said = report.human(souther.compiler.diag.SourceNameResolver.identity());

        assertTrue(said.contains("implemented"), () -> "the declarations say so: " + said);
        assertFalse(said.contains("this behavior has no body"),
                () -> "and nothing else in the report may say otherwise: " + said);
        assertTrue(said.contains("branch      not measured"),
                () -> "the measure says it has no number rather than saying nothing: " + said);
    }

    /** A {@code >->} composition still has no body of its own, which is the model's own answer. */
    @Test
    void aCompositionStillHasNoBodyOfItsOwn() {
        Compilation compilation = measured("""
                module example.comp

                data A = { n: Int }
                data B = { n: Int }
                data C = { n: Int }

                behavior one : (a: A) -> B
                    constructs B
                let one (a) = B { n = a.n }

                behavior two : (b: B) -> C
                    constructs C
                let two (b) = C { n = b.n }

                behavior both = one >-> two

                example both
                    | "one" : (A { n = 1 }) -> C { n = 1 }
                """);

        assertTrue(compilation.errors().isEmpty(), () -> "this one compiles: "
                + compilation.errors());
        Measure<Adequacy.BranchEvidence.Arms> measured =
                branchOf(compilation, "example.comp", "both").measured();

        Measure.NotApplicable<?> none = assertInstanceOf(Measure.NotApplicable.class, measured,
                () -> "its arms are its stages' and are measured there: " + measured);
        assertEquals(Adequacy.BranchEvidence.NoArms.NO_BODY, none.why());
    }

    /**
     * The coverage answers for every behavior of the module it was asked about, bar compositions.
     *
     * <p>A characterization of the contract as it stands, written because a reader depends on it.
     * {@code PartitionEvidence.NONE} says the model holds no subject for these measures, and the
     * two readers of this map reach it by a key being missing — so what a missing key means is part
     * of the answer, and it is written down nowhere the producer can be held to.
     *
     * <p>Which is the state of it and not the intent. The map is total over what it answers for
     * once the coverage answers for compositions itself, and this test inverts then: the reading
     * moves into the producer and the key stops carrying it (issue #996, stage 3).
     */
    @Test
    void theCoverageOmitsOnlyCompositions() {
        Compilation compilation = measured("""
                module example.mixed

                data A = { n: Int }
                data B = { n: Int }
                data C = { n: Int }

                behavior one : (a: A) -> B
                    constructs B
                let one (a) = B { n = a.n }

                behavior two : (b: B) -> C
                    constructs C
                let two (b) = C { n = b.n }

                behavior both = one >-> two

                behavior injected : (a: A) -> B

                example both
                    | "one" : (A { n = 1 }) -> C { n = 1 }
                """);

        Map<String, PartitionEvidence> answered =
                compilation.db().ask(new Adequacy.Coverage("example.mixed")).value();
        assertNotNull(answered, "the coverage answered");

        souther.compiler.check.Prepared module =
                compilation.db().ask(new Shapes.Prepared("example.mixed")).value();
        for (souther.compiler.ast.Hir.BehaviorDef behavior : module.behaviors()) {
            assertEquals(!module.isComposition(behavior), answered.containsKey(behavior.name()),
                    () -> "a behavior is in the coverage exactly when it is not a composition: "
                            + behavior.name() + " in " + answered.keySet());
        }
    }

    /** And a body that forks nowhere still owes no arm, which is the other settled nothing. */
    @Test
    void aBodyThatForksNowhereStillOwesNoArm() {
        Compilation compilation = measured("""
                module example.ok

                data Item = { sku: String }
                data Line = { sku: String }

                behavior pick : (item: Item) -> Line
                    constructs Line
                let pick (item) = Line { sku = item.sku }

                example pick
                    | "one" : (Item { sku = "a" }) -> Line { sku = "a" }
                """);

        assertTrue(compilation.errors().isEmpty(), () -> "this one compiles: "
                + compilation.errors());
        Measure<Adequacy.BranchEvidence.Arms> measured =
                branchOf(compilation, "example.ok", "pick").measured();

        Measure.NotApplicable<?> none = assertInstanceOf(Measure.NotApplicable.class, measured,
                () -> "the body is here and decides nothing: " + measured);
        assertEquals(Adequacy.BranchEvidence.NoArms.NO_ARM_OBLIGATIONS, none.why());
    }
}
