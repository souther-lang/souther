package souther.compiler.partition;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
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

    /** The lines that behavior's positions met, whosever the row at each point is. */
    private static java.util.List<souther.compiler.query.BorderAssessment> lines(
            String model, String behavior) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        java.util.List<souther.compiler.query.BorderAssessment> read =
                Adequacy.readingsOf(compilation.db(), "demo").get(behavior);
        assertNotNull(read, behavior + " was measured");
        return read;
    }

    private static PartitionEvidence measured(String model, String behavior) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> coverage =
                compilation.db().ask(new Adequacy.Coverage("demo")).value();
        assertNotNull(coverage, "the model under test compiles");
        PartitionEvidence evidence = coverage.get(behavior);
        assertNotNull(evidence, behavior + " was measured");
        return evidence;
    }

    /**
     * What a report is told stopped the reading at {@code position}.
     *
     * <p>Off the findings and not off the verdict. The verdict says whether anything divides the
     * position; what stopped the reading is a finding, made by whichever reader stopped, and a test
     * that read it back off the verdict would be asserting the reconstruction this arrangement
     * removes.
     */
    private static List<UndividedPosition.Reason> whyAt(PartitionEvidence evidence,
                                                       String position) {
        return evidence.notRead().stream()
                .filter(each -> each.at().equals(position))
                .map(PartitionEvidence.NotRead::reason)
                .toList();
    }

    /** And that the verdict says the model divides the position no way. */
    private static boolean absent(PartitionEvidence evidence, String position) {
        return evidence.notDerivable().stream()
                .anyMatch(each -> each.at().toString().equals(position) && each.isAbsent());
    }

    /** And that the verdict says nothing was established, without saying what stopped it. */
    private static boolean couldNotDerive(PartitionEvidence evidence, String position) {
        return evidence.notDerivable().stream()
                .anyMatch(each -> each.at().toString().equals(position)
                        && each.why() instanceof UndividedPosition.Why.CannotDerive);
    }

    /**
     * A declaration reachable from itself compiles, so its position is measured. Nothing about its
     * values could be worked out, and that is what is said — rather than that the model divides it
     * no way, which is a claim about the model this compiler is in no position to make.
     */
    @Test
    void aTypeThisCouldNotInterpretIsSaidToBeThatRatherThanAnAbsence() {
        PartitionEvidence measured = measured("""
                module demo
                data Ok
                data Cyclic = Cyclic
                behavior run : (x: Cyclic) -> Ok
                let run (x) = Ok
                """, "run");

        assertEquals(List.of(UndividedPosition.Reason.TYPE_UNRESOLVED), whyAt(measured, "x"));
        assertTrue(couldNotDerive(measured, "x"), "and nothing is established either way");
    }

    /**
     * The threshold is on a list element, and the element is a position the line is drawn on.
     *
     * <p>What the closure a combinator was handed compares is the element it was handed, and the
     * element of a list is a position of the input like any other. So the rule divides it, and the
     * report says what it divides it into rather than why nothing could be said.
     *
     * <p>What made this measurable is not a reading of collections. The position was already there
     * once the walk went into a sequence; what was missing was a name for what the closure's
     * parameter stood for, which the operation's own signature states and which the tree that runs
     * no longer holds.
     */
    @Test
    void aThresholdOnAnElementDividesTheElement() {
        PartitionEvidence measured = measured("""
                module demo
                data Ok
                data Item = { charge: Int }
                behavior run : (items: List<Item>) -> Ok
                let run (items) =
                    { guard List.length(List.filter((i) -> i.charge >= 21000, items)) < 1 else Ok
                      Ok }
                """, "run");

        assertEquals(List.of("items[*].charge"),
                measured.axes().stream().map(PartitionEvidence.AxisCoverage::path).toList(),
                "the element is where the line is drawn");
        // And the comparison outside the closure still says what it could not do. It names the
        // same position — the length it takes is of a list built from these elements — and a
        // position carries more than one statement, so one of them being read is no answer about
        // the other. What it says is that the rule is about a value made from what stands here:
        // the count of a filtered list is not a syntax nobody reads, and an author told that goes
        // looking for a spelling that was never the difficulty.
        assertEquals(List.of(UndividedPosition.Reason.RULE_ABOUT_A_DERIVED_VALUE),
                whyAt(measured, "items[*].charge"),
                () -> "said " + whyAt(measured, "items[*].charge"));
        assertFalse(couldNotDerive(measured, "items[*].charge"),
                "and the position is measured all the same");
    }

    /**
     * And a rule the second phase read and could do nothing with does not take the first phase's
     * answer away.
     *
     * <p>A body compares the length against a number outside what a length can be: the comparison
     * is understood — it is a threshold, on a term this measures — and it divides nothing, because
     * no value of the position is on the far side of it.
     *
     * <p>So the list comes back to the same place it was, which is a position nothing divides. What
     * is inside it is a position of its own and answers for itself, and is not what the list is
     * left with.
     */
    @Test
    void aRuleThatDividedNothingLeavesThePositionWithWhatItHad() {
        PartitionEvidence measured = measured("""
                module demo
                data Ok
                data Item = { charge: Int }
                behavior run : (items: List<Item>) -> Ok
                let run (items) = { guard List.length(items) < -1 else Ok
                    Ok }
                """, "run");

        assertEquals(List.of(), whyAt(measured, "items"),
                () -> "nothing stopped the reading of the list: " + whyAt(measured, "items"));
        assertTrue(absent(measured, "items"), "and the model divides it no way");
        // And what it holds is a position of its own, answering for itself. Nothing is written
        // about the elements here — the guard is on how many there are — so it divides no way
        // either, which is a conclusion about the model and not about this reading.
        assertTrue(absent(measured, "items[*].charge"),
                "the elements carry no rule, so nothing divides them");
    }

    /**
     * Issue #631. A sum under a name is that sum, so the position divides into its cases — where
     * before it came back as one the model divides no way, which is the opposite of what the
     * declaration says. Nothing about the reading of the model changed to make this true: the line
     * a {@code guard} drew on the same position always read through the name, and it is the reading
     * that asks what a position divides into that stopped there.
     *
     * <p>What the row is written as, and what a row already written is read back through, are
     * {@link ANameGoesBackOnTheWayItCameOffTest}'s — an axis needs all three.
     */
    @Test
    void aSumUnderANameDividesIntoTheCasesItWraps() {
        PartitionEvidence evidence = measured("""
                module demo
                data Ok
                data Rejected
                data Approved = { id: Int }
                data Decision = Approved | Rejected
                data DecisionN = Decision
                behavior run : (x: DecisionN) -> Ok
                let run (x) = Ok
                """, "run");

        assertEquals(List.of("Approved", "Rejected"), evidence.axes().get(0).classes());
        assertEquals(List.of(), evidence.notDerivable().stream()
                        .filter(each -> each.at().toString().equals("x")).toList(),
                "so there is nothing left to report about the position");
        // And what the case declares is under the case, at a position of its own. An `Int` nothing
        // bounds is one the model divides no way, which is a fact about the field and not about
        // the sum above it.
        assertTrue(absent(evidence, "x@Approved.id"));
    }

    /**
     * And the other side of that. A rule that measures the collection itself draws its line on the
     * collection, which is a position beside the one its elements are — so reaching into a sequence
     * does not take the sequence's own axis away, and this row is what stops that being forgotten.
     */
    @Test
    void aRuleMeasuringTheCollectionItselfIsStillMeasured() {
        String model = """
                module demo
                data Ok
                data Item = { charge: Int }
                behavior run : (items: List<Item>) -> Ok
                let run (items) = { guard List.length(items) < 3 else Ok
                    Ok }
                """;
        PartitionEvidence evidence = measured(model, "run");

        assertEquals(1, evidence.axes().size(), "the length is a line on the position itself");
        assertTrue(lines(model, "run").size() >= 1, "and it owes rows at its edges");
        assertEquals(List.of(), evidence.notDerivable().stream()
                        .filter(each -> each.at().toString().equals("items")).toList(),
                "so nothing is left to report about the collection itself");
    }
}
