package souther.compiler.reading;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Symbols;
import souther.compiler.core.Core;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.inputs.InputDomain;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.query.Scopes;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * A fork on an operator whose right aborts is a fork, and what is under its arms is read.
 *
 * <p>{@code a > 1 && unreachable} arrives at a value on every run that gets {@code a > 1} to fail:
 * the operator never evaluates its right there, so the expression comes to false and the fork below
 * it is reached. Read as strict in both its sides it arrives nowhere, and then the fork is a fork
 * nothing gets to — so both of its arms go unwalked, and every group standing in either of them is
 * one nobody is asked for.
 *
 * <p>Which is not a limit of what a group can be composed against. The way into the arm is the
 * comparison having failed, which is a decision a row is steered by and a place a run is recorded at,
 * so the group inside the arm is offered under it in the ordinary way.
 */
class AnArmUnderAnOperatorThatStopsEarlyIsWalkedTest {

    /** A meeting in the arm reached by the left of the operator settling the answer. */
    private static final String STOPS_ON_THE_LEFT = """
            module example.stops

            behavior fee : (a: Int, c: Int, d: Int) -> Int

            let fee (a, c, d) =
                if a > 1 && unreachable "no large a reaches here"
                    then 0
                    else (if c > 3 then 1 else 0) + (if d > 4 then 10 else 0)
            """;

    /**
     * The two forks in the arm are one meeting of two decisions, and it is offered.
     *
     * <p>One group and not none. Both operands of the sum vary two ways, which is the shape a row is
     * owed for; a reading that answered nothing here would be reporting that the body has no
     * combination to fill, which is a claim about the model and not about what could be read.
     */
    @Test
    void theMeetingInTheArmIsFound() {
        List<Interaction> found = read(STOPS_ON_THE_LEFT, "fee");
        assertEquals(List.of(List.of(2, 2)), shape(found),
                "the arm the comparison fails into holds one meeting of two two-way decisions");
    }

    /**
     * The way in is the comparison having failed, and not the arm it sent the run down.
     *
     * <p>A row is steered by getting the comparison to answer, so that is what the group is offered
     * under. Named by the arm instead it would place at no class of any input, and the group would go.
     */
    @Test
    void theWayInIsTheComparisonAndNotTheArm() {
        List<Interaction> found = read(STOPS_ON_THE_LEFT, "fee");
        assertEquals(List.of(List.of("Side")), reachKinds(found));
    }

    private static List<Interaction> read(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();
        assertNotNull(checked, "the model under test compiles");
        Core body = checked.behaviorBodies().get(behavior);
        assertNotNull(body, "the behavior under test has a body");
        Symbols symbols = Scopes.derived(compilation.db(), module).value();
        InputDomain inputs = compilation.db().ask(new Adequacy.Inputs(module)).value().get(behavior);
        return CoverageRead.of(behavior, body,
                CoverageSites.of(checked.behaviorBodies(), checked.decisions(),
                checked.supplied()), inputs, symbols).interactions();
    }

    /** The sizes of each group's factors, which is the shape of the space a row is owed for. */
    private static List<List<Integer>> shape(List<Interaction> found) {
        return found.stream()
                .map(group -> group.factors().stream().map(f -> f.outcomes().size()).toList())
                .toList();
    }

    /** What each group's way in is made of, said by the kind of condition each decision is. */
    private static List<List<String>> reachKinds(List<Interaction> found) {
        return found.stream()
                .map(group -> group.reach().stream()
                        .map(decision -> decision.constrains().getClass().getSimpleName())
                        .toList())
                .toList();
    }
}
