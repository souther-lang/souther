package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.coverage.AlignedObservation;
import souther.compiler.coverage.ComparisonEmissionIndex;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.coverage.Observation;
import souther.compiler.coverage.RecordedConditionOutcome;
import souther.compiler.core.Core;
import souther.compiler.partition.DecisionReading;
import souther.compiler.partition.ObservedInputs;
import souther.compiler.partition.RulesTaken;
import souther.compiler.partition.RunPlacement;
import souther.compiler.partition.ShownBy;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row recorded down a way the reading of the decision proved no input takes is that proof shown
 * wrong: kept as the proof it went against, said in the weakening of the rules the rows took, and
 * never a rule taken. Where the row is placed is asked apart from it — a row that also did every
 * condition of a rule is placed at the rule, and a row that went down two such ways went against
 * both proofs.
 *
 * <p>No row of a model goes there while the proof is right, and the proof is held to being right.
 * So the ways are the ones this compiler proves of the bodies below, and a run down them is
 * recorded here at the places the plan numbered for their conditions — which is what a row the
 * proof was wrong about would be recorded doing, and the one thing a test can do that a model
 * cannot.
 */
class ARowDownAWayNoInputTakesGoesAgainstTheProofTest {

    /** Below 5 is asked only of an input already above 10, which no input is. */
    private static final String ONE_WAY = """
            module demo
            behavior f : (x: Int) -> Int
            let f (x) = if x > 10 then (if x < 5 then 1 else 2) else 3
            """;

    /** The same clash on each of two inputs, apart: two proofs, and neither stands for the
     *  other. */
    private static final String TWO_WAYS = """
            module demo
            behavior f : (x: Int, y: Int) -> Int
            let f (x, y) = (if x > 10 then (if x < 5 then 1 else 2) else 3) + (if y > 10 then (if y < 5 then 1 else 2) else 3)
            """;

    /** The clash under {@code y > 0}, which the way no input takes does not consult, beside a rule
     *  that consults {@code y > 0} and nothing else. */
    private static final String A_RULE_BESIDE_THE_WAY = """
            module demo
            behavior f : (x: Int, y: Int) -> Int
            let f (x, y) = if y > 0 then (if x > 10 then (if x < 5 then 1 else 2) else 3) else 4
            """;

    @Test
    void aRunDownARuleOfTheBodyTakesThatRule() {
        Fixture at = new Fixture(ONE_WAY, 1);
        DecisionReading.Ruled rule = at.read().found().getFirst();

        assertEquals(new RulesTaken.WhichRule.TookThis(rule.rule()),
                at.placement().takenBy(at.aRunDown(rule)),
                "the control: a run recorded at a rule's conditions takes the rule");
        assertEquals(List.of(), at.placement().proofsGoneAgainst(at.aRunDown(rule)),
                "and went against no proof");
    }

    @Test
    void aRunDownTheWayNoInputTakesGoesAgainstTheProofAndIsPlacedNowhere() {
        Fixture at = new Fixture(ONE_WAY, 1);
        ObservedInputs run = at.aRunDown(at.way(0));

        assertEquals(List.of(at.way(0).rule()), at.placement().proofsGoneAgainst(run),
                "the run brought out every condition of the way as the way did");
        assertEquals(new RulesTaken.WhichRule.CouldNotTell(
                        RulesTaken.WhichRule.Why.ITS_WAY_IS_PROVED_TO_BE_TAKEN_BY_NO_INPUT),
                at.placement().takenBy(run),
                "and no rule past the way was read, so none is where it went");
    }

    @Test
    void theRowIsKeptAsTheProofAndCountedAtNoRule() {
        Fixture at = new Fixture(ONE_WAY, 1);
        Measure<DecisionEvidence.RowsPlaced> took = at.placing(at.aRunDown(at.way(0)));
        DecisionEvidence.RowsPlaced placed = took.made().orElseThrow(
                () -> new AssertionError("the row was read: " + took));

        assertEquals(Map.of(at.way(0).rule(), RowWitnesses.ANOTHER_ROW), placed.wentAgainst(),
                "the proof the row went against, with the row");
        assertEquals(Set.of(), placed.rules(), "and no rule taken by it");
        assertEquals(1, placed.rowsNotPlaced(), "the row is one no rule was placed at");
        assertWeakenedByTheProof(took);
    }

    @Test
    void aRunDownTwoWaysGoesAgainstBothProofs() {
        Fixture at = new Fixture(TWO_WAYS, 2);
        ObservedInputs run = at.aRunDown(at.way(0), at.way(1));

        assertEquals(List.of(at.way(0).rule(), at.way(1).rule()),
                at.placement().proofsGoneAgainst(run),
                "each proof is one of its own shown wrong, in the order the reading holds them");
        Measure<DecisionEvidence.RowsPlaced> took = at.placing(run);
        DecisionEvidence.RowsPlaced placed = took.made().orElseThrow(
                () -> new AssertionError("the row was read: " + took));
        assertEquals(List.of(at.way(0).rule(), at.way(1).rule()),
                new ArrayList<>(placed.wentAgainst().keySet()),
                "both kept, whichever the reading met first");
        assertEquals(1, placed.rowsNotPlaced(), "by the one row, placed at no rule");
        assertWeakenedByTheProof(took);
    }

    @Test
    void aRunAtARuleAndDownAWayIsPlacedAtTheRuleAndGoesAgainstTheProof() {
        Fixture at = new Fixture(A_RULE_BESIDE_THE_WAY, 1);
        DecisionReading.Ruled beside = at.read().found().stream()
                .filter(each -> each.rule().consulted().size() == 1).findFirst()
                .orElseThrow(() -> new AssertionError(
                        "a rule consulting y > 0 alone: " + at.read().found()));
        assertTrue(beside.rule().consulted().keySet().stream()
                        .noneMatch(at.way(0).rule().consulted()::containsKey),
                () -> "the rule and the way consult nothing in common: " + beside + " "
                        + at.way(0));
        ObservedInputs run = at.aRunDown(beside, at.way(0));

        assertEquals(new RulesTaken.WhichRule.TookThis(beside.rule()), at.placement().takenBy(run),
                "the run did every condition of the rule, so it is placed there");
        assertEquals(List.of(at.way(0).rule()), at.placement().proofsGoneAgainst(run),
                "and every condition of the way, so it went against the proof as well");
        Measure<DecisionEvidence.RowsPlaced> took = at.placing(run);
        DecisionEvidence.RowsPlaced placed = took.made().orElseThrow(
                () -> new AssertionError("the row was read: " + took));
        assertEquals(Set.of(beside.rule()), placed.rules(), "the rule is taken");
        assertEquals(1, placed.rowsPlaced(), "by the row, placed");
        assertEquals(Map.of(at.way(0).rule(), RowWitnesses.ANOTHER_ROW), placed.wentAgainst(),
                "and the proof it went against kept beside");
        assertWeakenedByTheProof(took);
    }

    /** The rules counted are short of whatever lies past a way gone down, and the measure says
     *  why. */
    private static void assertWeakenedByTheProof(Measure<DecisionEvidence.RowsPlaced> took) {
        assertInstanceOf(Measurement.Partial.class, took,
                "the rules counted are short of whatever lies past the way");
        assertTrue(took.weakening().causes().contains(new Weakening.DecisionOfRowUnreadable("f",
                        RulesTaken.WhichRule.Why.ITS_WAY_IS_PROVED_TO_BE_TAKEN_BY_NO_INPUT)),
                () -> "and says why: " + took.weakening());
    }

    /** A body compiled, its ways no input takes, and where its runs are recorded. */
    private static final class Fixture {

        private final DecisionReading read;
        private final CoverageSites.Plan plan;
        private final Core emitted;
        private final RunPlacement placement;

        Fixture(String model, int ways) {
            Compilation compilation = Compilation.ofSource(model, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            String module = compilation.modules().getFirst();
            read = compilation.db().ask(new Adequacy.Decides(module)).value().get("f").read();
            assertEquals(ways, read.impossible().size(),
                    () -> "the ways below 5 above 10 are proved: " + read.impossible());
            Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
            plan = checked.plan();
            emitted = checked.behaviorBodies().get("f");
            placement = new RunPlacement(RulesTaken.of(read, emitted, plan),
                    InputsOfTheBody.of(compilation, "f"));
        }

        DecisionReading read() {
            return read;
        }

        /** The {@code index}th way no input takes, as the reading holds them. */
        DecisionReading.Ruled way(int index) {
            return read.impossible().get(index).way();
        }

        RunPlacement placement() {
            return placement;
        }

        /** What the rows took, where the one row is {@code run}. */
        Measure<DecisionEvidence.RowsPlaced> placing(ObservedInputs run) {
            return DecisionEvidence.of("f", placement,
                    List.of(new WitnessedRow(run, RowWitnesses.ANOTHER_ROW)), WeakeningSet.none());
        }

        /** A row recorded bringing out each condition of every one of {@code ruled} as it says, at
         *  every copy the plan numbered. */
        ObservedInputs aRunDown(DecisionReading.Ruled... ruled) {
            ComparisonEmissionIndex comparisons = ComparisonEmissionIndex.ofBody(emitted, plan);
            Set<RecordedConditionOutcome> outcomes = new HashSet<>();
            for (DecisionReading.Ruled one : ruled) {
                for (ShownBy each : one.shownBy()) {
                    ShownBy.AtAnOutcome at = assertInstanceOf(ShownBy.AtAnOutcome.class, each,
                            "every condition of the body is a comparison of the input");
                    for (ComparisonEmissionIndex.EmittedComparison made
                            : comparisons.madeFor(at.construct())) {
                        ControlPlace.Outcome site =
                                plan.outcomeOf(made.occurrence(), at.held()).orElseThrow();
                        outcomes.add(new RecordedConditionOutcome(site.at().raw(), at.held()));
                    }
                }
            }
            AlignedObservation seen = plan.numbering().align(
                    new Observation(plan.numbering().identity(), Set.of(), outcomes));
            return InputsOfTheBody.aRunSeen(seen);
        }
    }
}
