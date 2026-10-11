package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.coverage.AlignedObservation;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.coverage.Observation;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.partition.AnswersDemanded;
import souther.compiler.partition.BehaviorInputs;
import souther.compiler.partition.ConditionOccurrence;
import souther.compiler.partition.DecidedCondition;
import souther.compiler.partition.DecisionCondition;
import souther.compiler.partition.DecisionReading;
import souther.compiler.partition.DecisionRule;
import souther.compiler.partition.RulesTaken;
import souther.compiler.partition.RunPlacement;
import souther.compiler.partition.ShownBy;
import souther.compiler.partition.WayToTheBorder;
import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A run recorded answering one condition of a rule both ways is not placed at that rule.
 *
 * <p>Where a run through a condition is recorded is a fact about the body, and what one run was
 * recorded doing there is a fact about the run. A place a run can pass more than once — a fork in a
 * function value applied per element — can be recorded going both ways in one run, and those
 * records are two answers and not one: the run went down more than one path there, and which of
 * them the row stands in is not something they say.
 *
 * <p>Asked of the rules directly, with the fork of a function value standing for a condition of
 * them. No reading of a body makes such a fork a condition of a rule today, so a body could not show
 * this; what is held is what a run is read as wherever a condition's place is one it can pass twice.
 */
class ARunThatAnsweredAConditionBothWaysTookNoOneRuleTest {

    private static final String MODEL = """
            module demo
            behavior f : (xs: List<Int>) -> List<Int>
            let f (xs) = List.map(x -> if x > 0 then 1 else 0, xs)
            """;

    private static final ConditionOccurrence AT = new ConditionOccurrence("f", 0);

    private static final DecisionCondition.AConditionNotRead CONDITION =
            new DecisionCondition.AConditionNotRead(AT,
                    new WhyNotTaken.OutsideDomain(WhyNotTaken.DomainLimit.A_QUANTITY_ON_NO_ORDER));

    private static final DecisionRule THEN = rule(true);

    private static final DecisionRule ELSE = rule(false);

    @Test
    void aRunDownOneArmTakesTheRuleOfThatArm() {
        Fixture at = new Fixture();
        assertEquals(new RulesTaken.WhichRule.TookThis(THEN),
                at.rules(THEN).takenBy(InputsOfTheBody.aRunSeen(at.seenDown(0))),
                "the control: one arm lit, and the rule that takes it that way");
    }

    @Test
    void aRunDownBothArmsTakesNeitherRuleThroughThem() {
        Fixture at = new Fixture();
        RulesTaken.WhichRule bothWays = new RulesTaken.WhichRule.CouldNotTell(
                RulesTaken.WhichRule.Why.A_CONDITION_CAME_OUT_BOTH_WAYS);
        assertEquals(bothWays, at.rules(THEN).takenBy(InputsOfTheBody.aRunSeen(at.seenDown(0, 1))),
                "the run went the rule's way and the other, so it is not shown to have taken it");
        assertEquals(bothWays, at.rules(THEN, ELSE).takenBy(InputsOfTheBody.aRunSeen(at.seenDown(0, 1))),
                "and with a rule for each arm it took neither, rather than both");
    }

    private static DecisionRule rule(boolean held) {
        return new DecisionRule(Map.of(CONDITION, new DecidedCondition.Unread(CONDITION, held)));
    }

    /** The body above, its plan, and the fork of its function value. */
    private static final class Fixture {

        private final Bodies.Elaborated checked;
        private final CoverageSites.Plan plan;
        private final BehaviorInputs inputs;
        private final List<ControlPlace.Arm> arms = new ArrayList<>();

        Fixture() {
            Compilation compilation = Compilation.ofSource(MODEL, "Main");
            inputs = InputsOfTheBody.of(compilation, "f");
            checked = compilation.db().ask(new Bodies.Checked(compilation.modules().get(0)))
                    .value();
            plan = checked.plan();
            for (CoverageSites.ArmSite each : plan.arms("f")) {
                arms.add(each.place());
            }
            assertEquals(2, arms.size(), "the one fork of the function value, with its two arms");
        }

        /** The rules {@code taken}, the first down the fork's first arm and so on. */
        RunPlacement rules(DecisionRule... taken) {
            ModelOccurrence fork = ModelOccurrence.statedAt(arms.get(0).arm().fork()).orElseThrow();
            List<DecisionReading.Ruled> found = new ArrayList<>();
            for (int i = 0; i < taken.length; i++) {
                found.add(new DecisionReading.Ruled(taken[i],
                        List.of(new ShownBy.AtAnArm(fork, partOf(taken[i]))),
                        WayToTheBorder.UNTOUCHED, AnswersDemanded.NOTHING, true));
            }
            return new RunPlacement(RulesTaken.of(new DecisionReading("f", found,
                    new DecisionReading.Enumeration.Complete()),
                    checked.behaviorBodies().get("f"), plan), inputs);
        }

        /** A run recorded down the arms {@code parts} of the fork. */
        AlignedObservation seenDown(int... parts) {
            Set<Integer> lit = new HashSet<>();
            for (int part : parts) {
                for (ControlPlace.Arm each : arms) {
                    if (each.arm().part() == part) {
                        lit.add(each.probe().orElseThrow().raw());
                    }
                }
            }
            return plan.numbering().align(
                    new Observation(plan.numbering().identity(), lit, Set.of()));
        }

        private static int partOf(DecisionRule rule) {
            return rule.equals(THEN) ? 0 : 1;
        }
    }
}
