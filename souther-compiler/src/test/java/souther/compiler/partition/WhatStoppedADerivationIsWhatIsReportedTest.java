package souther.compiler.partition;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Models that end a derivation different ways, each reported as what actually happened.
 *
 * <p>They are here together because they are the failure modes the protocol is for, and each
 * of them was one sentence before: a position the model does not divide. Read as a table, the rows
 * say that the report follows the evidence — what was found, what could not be interpreted, what
 * could not be reached, and what a rule in a body answered for after the structure ran out.
 */
class WhatStoppedADerivationIsWhatIsReportedTest {

    private static PartitionEvidence measured(String model, String behavior) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage("demo")).value();
        assertNotNull(coverage, "the model under test compiles");
        PartitionEvidence evidence = coverage.get(behavior);
        assertNotNull(evidence, behavior + " was measured");
        return evidence;
    }

    private static UndividedPosition.Why whyAt(PartitionEvidence evidence, String position) {
        return evidence.notDerivable().stream()
                .filter(each -> each.at().toString().equals(position))
                .map(UndividedPosition::why)
                .findFirst().orElse(null);
    }

    /**
     * A declaration reachable from itself compiles, so its position is measured. Nothing about its
     * values could be worked out, and that is what is said — rather than that the model divides it
     * no way, which is a claim about the model this compiler is in no position to make.
     */
    @Test
    void aTypeThisCouldNotInterpretIsSaidToBeThatRatherThanAnAbsence() {
        UndividedPosition.Why why = whyAt(measured("""
                module demo
                data Ok
                data Cyclic = Cyclic
                behavior run : (x: Cyclic) -> Ok constructs Ok
                let run (x) = Ok
                """, "run"), "x");

        assertEquals(new UndividedPosition.Why.CannotDerive(
                UndividedPosition.Reason.TYPE_UNRESOLVED), why);
    }

    /**
     * Issue #626. The threshold is on a list element, and the elements cannot be reached. What was
     * reported is that the comparison is written in a form this does not read, which is a different
     * cause — the form is read perfectly well, and it names a position under a collection.
     */
    @Test
    void aThresholdOnAnElementSaysTheElementsCouldNotBeReached() {
        UndividedPosition.Why why = whyAt(measured("""
                module demo
                data Ok
                data Item = { charge: Int }
                behavior run : (items: List<Item>) -> Ok constructs Ok
                let run (items) =
                    { guard List.length(List.filter((i) -> i.charge >= 21000, items)) < 1 else Ok
                      Ok }
                """, "run"), "items");

        assertEquals(new UndividedPosition.Why.CannotDerive(
                UndividedPosition.Reason.UNSUPPORTED_TRAVERSAL), why);
    }

    /**
     * And the other side of that. A collection's elements cannot be reached either, and a rule that
     * measures the collection itself still draws its line — so a block is what a position is left
     * with rather than a verdict on it, and this row is what stops that being forgotten.
     */
    @Test
    void aRuleMeasuringTheCollectionItselfIsStillMeasured() {
        PartitionEvidence evidence = measured("""
                module demo
                data Ok
                data Item = { charge: Int }
                behavior run : (items: List<Item>) -> Ok constructs Ok
                let run (items) = { guard List.length(items) < 3 else Ok
                    Ok }
                """, "run");

        assertEquals(1, evidence.axes().size(), "the length is a line on the position itself");
        assertTrue(evidence.boundaries().size() >= 1, "and it owes rows at its edges");
        assertEquals(List.of(), evidence.notDerivable(),
                "so nothing is left to report about the position");
    }
}
