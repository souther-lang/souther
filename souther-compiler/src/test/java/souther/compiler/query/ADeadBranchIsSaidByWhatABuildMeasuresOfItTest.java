package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.ACompiledModel;
import souther.compiler.WhereItSits;
import souther.compiler.diag.Primary;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A branch nothing reaches is said where every place it stands is proven to be reached by nothing,
 * and a build that measures some behaviors proves it of those.
 *
 * <p>An arm written in a behavior's own body stands in that behavior, so measuring the behavior is
 * all that proves it. One written in a helper stands in every behavior that calls the helper, and
 * one of them that was not measured leaves it unproven, whatever the others say.
 */
class ADeadBranchIsSaidByWhatABuildMeasuresOfItTest {

    /** Line 7 is dead in `own` and stands nowhere else; line 4 is dead in `own`, which hands the
     *  helper an age, and is taken in `other`, which hands it any number; line 13 is dead in both
     *  behaviors that hand `doubled` an age. */
    private static final String MODEL = """
            module m
            data Age = Int
                invariant value >= 0
            let sized (n: Int): Int = if n < 0 then 1 else 2
            behavior own : (x: Age) -> Int
            let own (x) =
                (if x.value < 0 then 1 else 2) + sized(x.value)
            behavior other : (n: Int) -> Int
            let other (n) = sized(n)
            behavior one : (x: Age) -> Int
            let one (x) = doubled(x.value)
            let doubled (n: Int): Int =
                if n < 0 then 1 else n * 2
            behavior two : (x: Age) -> Int
            let two (x) = doubled(x.value)
            """;

    private static List<Integer> linesSaid(Adequacy.Choice choice) {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.choose(choice);
        compilation.measure(Adequacy.Asked.NOTHING);
        ACompiledModel.compiles(compilation);
        compilation.answerEverything();
        return compilation.warnings().stream()
                .filter(each -> each.diagnostic().code().equals("E1327"))
                .map(each -> ((Primary.InSource) each.diagnostic().primary()).place().region())
                .map(region -> WhereItSits.in(MODEL, region).start().line()).sorted().toList();
    }

    @Test
    void measuredWholeEveryOneIsSaid() {
        assertEquals(List.of(7, 13), linesSaid(Adequacy.Choice.EVERYTHING));
    }

    /** Naming the module measures every behavior of it. */
    @Test
    void namingTheModuleSaysWhatMeasuringItSays() {
        assertEquals(List.of(7, 13), linesSaid(new Adequacy.Choice("m", null)));
    }

    @Test
    void anArmOfABehaviorsOwnBodyIsSaidWhereThatBehaviorIsMeasured() {
        assertEquals(List.of(7), linesSaid(new Adequacy.Choice(null, "own")));
    }

    /** Another behavior, unmeasured, calls the helper: it may take the arm. */
    @Test
    void anArmOfAHelperAnUnmeasuredBehaviorCallsIsNotSaid() {
        assertEquals(List.of(), linesSaid(new Adequacy.Choice(null, "one")));
    }

    @Test
    void nothingIsSaidOfAModuleOutsideTheChoice() {
        assertEquals(List.of(), linesSaid(new Adequacy.Choice("another", null)));
    }
}
