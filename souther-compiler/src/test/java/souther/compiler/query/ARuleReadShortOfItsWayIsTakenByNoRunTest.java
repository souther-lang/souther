package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.coverage.AlignedObservation;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.coverage.Observation;
import souther.compiler.partition.AnswersDemanded;
import souther.compiler.partition.DecisionReading;
import souther.compiler.partition.DecisionRule;
import souther.compiler.partition.RulesTaken;
import souther.compiler.partition.WayToTheBorder;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A rule read with fewer conditions than its way turns on is one no run is placed at.
 *
 * <p>What a run is checked against is the conditions the path carries. Where the path is not whole,
 * a run seen doing all of them has not been shown to have taken the rule, and a path with none left
 * is matched by every run — which puts every run at that rule as well as at the one it took.
 *
 * <p>Held beside the rule with no conditions that is whole, because the two are not the same
 * thing: a body that draws no distinction has one rule and every run takes it. Asking whether the
 * path is empty would set that one aside too.
 */
class ARuleReadShortOfItsWayIsTakenByNoRunTest {

    /** A body with no fork, which is all a plan and a tree are needed for here. */
    private static final String MODEL = """
            module demo
            data Yes
            behavior decides : (a: Int) -> Yes
            let decides (a) = Yes
            """;

    private static final DecisionRule NO_DISTINCTION = new DecisionRule(Map.of());

    @Test
    void aPathThatIsNotWholeIsSetAside() {
        assertEquals(new RulesTaken.WhichRule.CouldNotTell(
                        RulesTaken.WhichRule.Why.NO_RULE_IS_RECOGNISABLE),
                takenByARunThatSawNothing(false));
    }

    @Test
    void aWholePathWithNoConditionIsTakenByEveryRun() {
        assertEquals(new RulesTaken.WhichRule.TookThis(NO_DISTINCTION),
                takenByARunThatSawNothing(true));
    }

    /** Which rule a run that was seen doing nothing took, of a body read as the one rule above. */
    private static RulesTaken.WhichRule takenByARunThatSawNothing(boolean whole) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        String module = compilation.modules().get(0);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        CoverageSites.Plan plan = checked.plan();
        DecisionReading read = new DecisionReading("decides", List.of(new DecisionReading.Ruled(
                NO_DISTINCTION, List.of(), WayToTheBorder.UNTOUCHED, AnswersDemanded.NOTHING,
                whole)), new DecisionReading.Enumeration.Complete());
        RulesTaken rules = RulesTaken.of(read, checked.behaviorBodies().get("decides"), plan);
        AlignedObservation nothing = plan.numbering().align(
                new Observation(plan.numbering().identity(), Set.of(), Set.of()));
        return rules.takenBy(nothing);
    }
}
