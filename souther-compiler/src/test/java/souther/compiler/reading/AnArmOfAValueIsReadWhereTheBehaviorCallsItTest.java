package souther.compiler.reading;

import org.junit.jupiter.api.Test;
import souther.compiler.coverage.ArmProbe;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.coverage.CoverageSites;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An arm in a value the backend emits as a method is read where a behavior's run goes into it.
 *
 * <p>The plan owes a behavior the arms of every value it calls, so the reading of the behavior has
 * to reach them — in the value's method, under what holds where the behavior calls it. A value
 * takes no input, so whether a run gets to one of its arms is whether it gets to a call of the
 * value: called only where no run gets, its arms are reached by none, and what was decided on the
 * way to the call is known inside it. A value called from two places is reached wherever either
 * call is, whichever of the two the walk meets last.
 */
class AnArmOfAValueIsReadWhereTheBehaviorCallsItTest {

    private static final String MODULE = "example.values";

    private static final String MODEL = """
            module example.values
            data N = { v: Int }
            data R = { out: Int }

            let big = if List.length([1, 2, 3]) > 2 then 1 else 0

            let bigger = if big > 0 then 2 else 3

            let summed = List.sum(List.map(x -> x + big, [1, 2]))

            let guarded = {
                guard List.length([1, 2]) > 1 else 0
                5
            }

            let zero = List.get(0, [ 0 ]) |> Option.withDefault(0)

            behavior nowhere : (n: N) -> R
                constructs R
            let nowhere (n) = {
                let c = n.v > 0
                R { out = if c then (if c then n.v else big) else n.v }
            }

            behavior reachedFirst : (n: N) -> R
                constructs R
            let reachedFirst (n) = {
                let c = n.v > 0
                R { out = if c then (if c then big else summed) else n.v }
            }

            behavior reachedLast : (n: N) -> R
                constructs R
            let reachedLast (n) = {
                let c = n.v > 0
                R { out = if c then (if c then summed else big) else n.v }
            }

            behavior through : (n: N) -> R
                constructs R
            let through (n) = R { out = n.v + bigger + summed + guarded + zero }

            example through
                | "x" : (N { v = 1 }) -> R { out = 13 }
            """;

    @Test
    void everyArmThePlanOwesABehaviorIsRead() {
        Model model = Model.of();
        for (String behavior : List.of("nowhere", "reachedFirst", "reachedLast", "through")) {
            assertEquals(model.plan.arms(behavior).stream().map(CoverageSites.ArmSite::index)
                            .toList(),
                    List.copyOf(model.reads.get(behavior).arms().keySet()),
                    "`" + behavior + "` is read at every arm the plan owes it");
        }
        // Its own, one value it hands another, one it calls inside a function, one with a guard,
        // and one through a library function that branches.
        Set<String> owners = model.plan.arms("through").stream()
                .map(CoverageSites.ArmSite::body).collect(Collectors.toSet());
        assertEquals(Set.of("big", "bigger", "guarded", "zero"), owners);
        assertEquals(5, model.checked.run("through").methods().size(),
                "a run of `through` goes through every value it calls, `summed` holding no arm");
    }

    @Test
    void aValueCalledOnlyWhereNoRunGetsHasArmsNoRunReaches() {
        Model model = Model.of();
        for (ArmProbe arm : model.armsOf("nowhere", "big")) {
            assertEquals(new PathAccess.Unreachable(
                            PathAccess.Unreachable.Why.CONTRADICTS_WHAT_ALREADY_HELD),
                    model.reads.get("nowhere").armAt(arm));
        }
    }

    @Test
    void aValueCalledTwoWaysIsReachedWhereEitherCallIs() {
        Model model = Model.of();
        // `big` is called by the behavior and inside the function `summed` applies, one of the two
        // under a way no run takes. The behavior's body is read before `summed`, so the call no
        // run gets to is met last from `reachedFirst` and first from `reachedLast`.
        for (String behavior : List.of("reachedFirst", "reachedLast")) {
            for (ArmProbe arm : model.armsOf(behavior, "big")) {
                assertInstanceOf(PathAccess.Unsupported.class,
                        model.reads.get(behavior).armAt(arm),
                        "`big` is reached from `" + behavior + "` by the call some run gets to");
            }
        }
    }

    @Test
    void whatIsDecidedOnTheWayToTheCallHoldsInsideTheValue() {
        Model model = Model.of();
        // A value's own fork is on nothing the input names, so its arms are told no way in a row
        // could be steered along; what the call was made under shows in the ways a run takes.
        Set<ArmProbe> inBig = Set.copyOf(model.armsOf("reachedFirst", "big"));
        boolean bothKnown = model.reads.get("reachedFirst").taken().stream()
                .anyMatch(way -> way.decisions().stream()
                        .anyMatch(d -> d.constrains() instanceof Condition.Side side
                                && side.held())
                        && way.decisions().stream()
                        .anyMatch(d -> d.claims().at() instanceof ControlPlace.Arm arm
                                && arm.probe().isPresent() && inBig.contains(arm.probe().get())));
        assertTrue(bothKnown, "a way out of `big`'s fork holds the comparison of `n.v` the call"
                + " was made under: " + model.reads.get("reachedFirst").taken());
    }

    @Test
    void aGuardInAValueSaysWhereTheRestOfItsBlockGoesOn() {
        Model model = Model.of();
        List<ArmProbe> inGuarded = model.armsOf("through", "guarded");
        assertEquals(2, inGuarded.size());
        Map<ArmProbe, TheRestOfTheBlock> rest = model.reads.get("through").restOfTheBlock();
        assertEquals(Set.of(inGuarded.get(1)), rest.keySet(),
                "the arm leaving the guard is told where the block goes on");
        assertEquals(inGuarded.get(0), rest.get(inGuarded.get(1)).arm());
    }

    private record Model(Bodies.Elaborated checked, CoverageSites.Plan plan,
                         Map<String, CoverageRead.Read> reads) {

        static Model of() {
            Compilation compilation = Compilation.ofSource(MODEL, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            assertEquals(List.of(), compilation.errors().stream()
                            .map(e -> e.diagnostic().code()).toList(),
                    "the model under test compiles");
            Bodies.Elaborated checked = compilation.db().ask(new Bodies.Observable(MODULE)).value();
            return new Model(checked, checked.plan(),
                    compilation.db().ask(new Adequacy.Meets(MODULE)).value());
        }

        /** The arms of {@code value} the plan owes {@code behavior}, in the order it holds them. */
        List<ArmProbe> armsOf(String behavior, String value) {
            return plan.arms(behavior).stream().filter(arm -> arm.body().equals(value))
                    .map(CoverageSites.ArmSite::index).toList();
        }
    }
}
