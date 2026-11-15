package souther.compiler.reading;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;
import souther.compiler.core.Core;
import souther.compiler.coverage.ControlClaim;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.flow.Arrival;
import souther.compiler.flow.Completeness;
import souther.compiler.flow.Provenance;
import souther.compiler.flow.Truth;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a row has to be to settle a decision one way is the union of the ways that reach it, so an
 * outcome is told those ways only where every one of them was written down whole.
 *
 * <p>One way the naming could not write is a part of the region that the others do not state. Told
 * the rest as if they were all, the outcome would be narrower than the rows that settle it, and a
 * combination with a decision on those rows would not exist.
 */
class AnOutcomeIsToldItsWaysOnlyWhereEveryWayIsWrittenDownTest {

    private static final String MODEL = """
            module m

            behavior pick : (flag: Bool) -> Int
            let pick (flag) = if flag then 1 else 2
            """;

    @Test
    void twoWaysWrittenWholeAreWhatARowHasToBe() {
        Fixture fixture = new Fixture();

        List<Outcome> outcomes = Meetings.outcomesFrom(List.of(
                fixture.reaching(Completeness.COMPLETE, 0),
                fixture.reaching(Completeness.COMPLETE, 1)));

        assertEquals(1, outcomes.size(), "two ways a run is not seen to tell apart are one outcome");
        assertEquals(2, waysOf(outcomes.getFirst()).size(), "and it is told both");
    }

    @Test
    void aWayNotWrittenWholeLeavesTheOutcomeOfferedAndItsRegionUnsaid() {
        Fixture fixture = new Fixture();

        List<Outcome> outcomes = Meetings.outcomesFrom(List.of(
                fixture.reaching(Completeness.COMPLETE, 0),
                fixture.reaching(Completeness.PARTIAL, 1)));

        assertEquals(1, outcomes.size(), "the outcome is reached whole by one way, so it is offered");
        assertTrue(waysOf(outcomes.getFirst()).isEmpty(),
                "but not told the one way: the other is rows it does not state");
    }

    @Test
    void anOutcomeOnlyWaysNotWrittenWholeReachAreNotOffered() {
        Fixture fixture = new Fixture();

        assertTrue(Meetings.outcomesFrom(List.of(fixture.reaching(Completeness.PARTIAL, 0)))
                        .isEmpty(),
                "what no way written whole reaches is not an outcome a row is steered to");
    }

    private static List<List<Condition>> waysOf(Outcome outcome) {
        return ((Condition.Arm) outcome.holds().getFirst().constrains()).comesOutBy();
    }

    /** Arms of one fork, standing for the outcome and for conditions that reach it. */
    private static final class Fixture {

        private final ControlPlace.Arm[] arms;

        Fixture() {
            Compilation compilation = ACompiledModel.answered(MODEL);
            Bodies.Elaborated checked = compilation.db()
                    .ask(new Bodies.Checked(compilation.modules().get(0))).value();
            arms = checked.plan().armsOf(forkIn(checked.behaviorBodies().get("pick")));
        }

        /** An arrival at the outcome that is the arm {@code arm} was taken, by a way written as
         *  the condition that arm {@code way} was taken. */
        Arrival<Outcome> reaching(Completeness completeness, int way) {
            Outcome seen = outcomeOf(0);
            Outcome path = outcomeOf(way);
            return new Arrival<>(Truth.FALSE, new Provenance<>(path, completeness, List.of(), seen));
        }

        private Outcome outcomeOf(int arm) {
            return new Outcome(List.of(new Decision(
                    new Condition.Arm(arms[arm].arm(), Optional.empty()),
                    ControlClaim.of(arms[arm]).orElseThrow())));
        }

        private static Core forkIn(Core body) {
            List<Core> found = new ArrayList<>();
            collect(body, found);
            return found.getFirst();
        }

        private static void collect(Core e, List<Core> found) {
            if (e instanceof Core.If) {
                found.add(e);
            }
            Core.forEachChild(e, child -> collect(child, found));
        }
    }
}
