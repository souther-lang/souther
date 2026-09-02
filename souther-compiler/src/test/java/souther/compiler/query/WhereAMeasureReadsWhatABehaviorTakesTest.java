package souther.compiler.query;

import org.junit.jupiter.api.Test;

import souther.compiler.ast.Hir;
import souther.compiler.check.Prepared;
import souther.compiler.check.Sig;
import souther.compiler.inputs.InputDomain;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;

/**
 * Where what a behavior takes is read is the boundary's answer, and a composition's is at its
 * stages.
 *
 * <p>Two behaviors of one module, and the difference between them is not that one of them could
 * not be read. {@code issue} takes an input of its own and it is read here; {@code whole} takes
 * what its first stage takes and is measured there. Both have a signature and both are measured,
 * so neither is short of anything.
 *
 * <p>Which is the thing an input with no positions could not say. Handed one for the composition,
 * every measure that reads the boundary was told the model divides it nowhere — the same answer a
 * behavior whose rules part nothing gets, and the same answer a behavior nobody could read the
 * input of got.
 */
class WhereAMeasureReadsWhatABehaviorTakesTest {

    private static final String MODULE = "example.stages";

    private static final String MODEL = """
            module example.stages

            data Amount = Int
                invariant value >= 0
            data Invoice = { amount: Amount }
            data Receipt = { n: Int }

            behavior issue : (a: Amount) -> Invoice
                constructs Invoice
            let issue (a) = Invoice { amount = a }

            behavior receipt : (i: Invoice) -> Receipt
                constructs Receipt
            let receipt (i) = Receipt { n = 1 }

            behavior whole = issue >-> receipt
            """;

    private static Compilation measured() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation;
    }

    private static Hir.BehaviorDef declared(Compilation compilation, String name) {
        Prepared prepared = compilation.db().ask(new Shapes.Prepared(MODULE)).value();
        assertNotNull(prepared, "the model under test compiles");
        return prepared.behaviors().stream().filter(each -> each.name().equals(name))
                .findFirst().orElseThrow();
    }

    private static BoundaryForMeasurement boundaryOf(Compilation compilation, String name) {
        Map<String, Sig> sigs = compilation.db().ask(new Bodies.Signatures(MODULE)).value();
        Map<String, InputDomain> read = compilation.db().ask(new Adequacy.Inputs(MODULE)).value();
        assertNotNull(sigs, "the signatures answered");
        assertNotNull(read, "and so did the reading of what the behaviors take");
        return BoundaryForMeasurement.of(sigs, read, declared(compilation, name));
    }

    /** A declared behavior's input is read here, and the reading is the one the module made. */
    @Test
    void aDeclaredBehaviorsInputIsReadWhereItIsDeclared() {
        Compilation compilation = measured();
        InputDomain read =
                compilation.db().ask(new Adequacy.Inputs(MODULE)).value().get("issue");

        BoundaryForMeasurement.Derived derived = assertInstanceOf(
                BoundaryForMeasurement.Derived.class, boundaryOf(compilation, "issue"));
        InputForMeasurement.Local local =
                assertInstanceOf(InputForMeasurement.Local.class, derived.input());

        assertEquals("issue", local.spec().name(),
                "the reading is paired with the declaration it was read from");
        assertSame(read, local.domain(), "and it is the module's reading, not one made beside it");
    }

    /**
     * A composition has no reading of its own, and that is what it says.
     *
     * <p>Not an input with no positions. The reading of the module holds no entry for it — there
     * was nothing to walk — and what a measure is told is where the input is, so nothing here is
     * an answer about what the model does or does not divide.
     */
    @Test
    void aCompositionIsMeasuredAtItsStages() {
        Compilation compilation = measured();

        assertNull(compilation.db().ask(new Adequacy.Inputs(MODULE)).value().get("whole"),
                "nothing walked an input of the composition's own");

        BoundaryForMeasurement.Derived derived = assertInstanceOf(
                BoundaryForMeasurement.Derived.class, boundaryOf(compilation, "whole"),
                "its signature was worked out, so its boundary was");
        assertSame(InputForMeasurement.AtStages.INSTANCE, derived.input());
    }

    /**
     * And what the signature measure takes from a reading, it does not take from the composition.
     *
     * <p>The one thing that count reads off an input is which declared cases the rules refuse. A
     * composition has no positions of its own to refuse anything at, which is an answer this makes
     * without a reading — asked for one it would have to be handed an empty one, and the count
     * would be reading "nothing is refused" off a reading that read nothing.
     */
    @Test
    void andACompositionIsCountedWithoutOne() {
        Compilation compilation = measured();

        assertSame(InputCaseExclusions.NothingIsRefusedHere.INSTANCE,
                InputCaseExclusions.of(InputForMeasurement.AtStages.INSTANCE));

        Adequacy.SignatureEvidence signature = compilation.db()
                .ask(new Adequacy.Witnesses(MODULE)).value().get("whole");
        assertNotNull(signature, "the signature measure answered for the composition");
        assertFalse(signature.notMeasurable(),
                "and it is a measure that was made, not one short of its boundary");
    }
}
