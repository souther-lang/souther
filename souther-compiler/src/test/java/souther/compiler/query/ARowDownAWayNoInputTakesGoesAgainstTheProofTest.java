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

import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row recorded down a way the reading of the decision proved no input takes is that proof shown
 * wrong: kept as the proof it went against, placed at no rule, and said in the weakening of the
 * rules the rows took — never lost among the rows nothing could place, and never a rule taken.
 *
 * <p>No row of a model goes there while the proof is right, and the proof is held to being right.
 * So the way is the one this compiler proves of the body below, and the run down it is recorded
 * here at the places the plan numbered for its conditions — which is what a row the proof was
 * wrong about would be recorded doing, and the one thing a test can do that a model cannot.
 */
class ARowDownAWayNoInputTakesGoesAgainstTheProofTest {

    /** Below 5 is asked only of an input already above 10, which no input is. */
    private static final String MODEL = """
            module demo
            behavior f : (x: Int) -> Int
            let f (x) = if x > 10 then (if x < 5 then 1 else 2) else 3
            """;

    @Test
    void aRunDownARuleOfTheBodyTakesThatRule() {
        Fixture at = new Fixture();
        DecisionReading.Ruled rule = at.read().found().getFirst();

        assertEquals(new RulesTaken.WhichRule.TookThis(rule.rule()),
                at.placement().takenBy(at.aRunDown(rule)),
                "the control: a run recorded at a rule's conditions takes the rule");
    }

    @Test
    void aRunDownTheWayNoInputTakesIsTheProofItWentAgainst() {
        Fixture at = new Fixture();

        assertEquals(new RulesTaken.WhichRule.AgainstAProof(at.way().way().rule()),
                at.placement().takenBy(at.aRunDown(at.way().way())),
                "the run brought out every condition of the way as the way did");
    }

    @Test
    void theRowIsKeptAsTheProofAndCountedAtNoRule() {
        Fixture at = new Fixture();
        Measure<DecisionEvidence.RowsPlaced> took = DecisionEvidence.of("f", at.placement(),
                List.of(new WitnessedRow(at.aRunDown(at.way().way()), RowWitnesses.ANOTHER_ROW)),
                WeakeningSet.none());
        DecisionEvidence.RowsPlaced placed = took.made().orElseThrow(
                () -> new AssertionError("the row was read: " + took));

        assertEquals(Map.of(at.way().way().rule(), RowWitnesses.ANOTHER_ROW),
                placed.wentAgainst(),
                "the proof the row went against, with the row");
        assertEquals(Set.of(), placed.rules(), "and no rule taken by it");
        assertEquals(1, placed.rowsNotPlaced(), "the row is one no rule was placed at");
        assertInstanceOf(Measurement.Partial.class, took,
                "the rules counted are short of whatever lies past the way");
        assertTrue(took.weakening().causes().contains(new Weakening.DecisionOfRowUnreadable("f",
                        RulesTaken.WhichRule.Why.ITS_WAY_IS_PROVED_TO_BE_TAKEN_BY_NO_INPUT)),
                () -> "and says why: " + took.weakening());
    }

    /** The body above compiled, its one way no input takes, and where its runs are recorded. */
    private static final class Fixture {

        private final DecisionReading read;
        private final DecisionReading.ImpossiblePath way;
        private final CoverageSites.Plan plan;
        private final Core emitted;
        private final RunPlacement placement;

        Fixture() {
            Compilation compilation = Compilation.ofSource(MODEL, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            String module = compilation.modules().getFirst();
            read = compilation.db().ask(new Adequacy.Decides(module)).value().get("f").read();
            assertEquals(1, read.impossible().size(),
                    () -> "the way below 5 above 10 is proved: " + read.impossible());
            way = read.impossible().getFirst();
            Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
            plan = checked.plan();
            emitted = checked.behaviorBodies().get("f");
            placement = new RunPlacement(RulesTaken.of(read, emitted, plan),
                    InputsOfTheBody.of(compilation, "f"));
        }

        DecisionReading read() {
            return read;
        }

        DecisionReading.ImpossiblePath way() {
            return way;
        }

        RunPlacement placement() {
            return placement;
        }

        /** A row recorded bringing out each condition of {@code ruled} as it says, at every copy
         *  the plan numbered. */
        ObservedInputs aRunDown(DecisionReading.Ruled ruled) {
            ComparisonEmissionIndex comparisons = ComparisonEmissionIndex.ofBody(emitted, plan);
            Set<RecordedConditionOutcome> outcomes = new HashSet<>();
            for (ShownBy each : ruled.shownBy()) {
                ShownBy.AtAnOutcome at = assertInstanceOf(ShownBy.AtAnOutcome.class, each,
                        "every condition of the body is a comparison of the input");
                for (ComparisonEmissionIndex.EmittedComparison made
                        : comparisons.madeFor(at.construct())) {
                    ControlPlace.Outcome site =
                            plan.outcomeOf(made.occurrence(), at.held()).orElseThrow();
                    outcomes.add(new RecordedConditionOutcome(site.at().raw(), at.held()));
                }
            }
            AlignedObservation seen = plan.numbering().align(
                    new Observation(plan.numbering().identity(), Set.of(), outcomes));
            return InputsOfTheBody.aRunSeen(seen);
        }
    }
}
