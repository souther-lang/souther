package souther.compiler.coverage;

import org.junit.jupiter.api.Test;
import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A value emitted as a method is a body with its own forks, and what decides each of them is read
 * for it whether or not a behavior of its module names it: which rule a call was handed is as much
 * a part of that as which declaration wrote the fork.
 */
class AValueMethodIsReadWithWhatItsCallsWereHandedTest {

    /** The fork is the helper's and it decides by the rule the value hands it, so the fork is
     * settled only once it is known which rule that was. */
    private static final String MODEL = """
            module limits exposing ( ceiling )

            let choose (p: (Int) -> Bool, n: Int): Int =
                if p(n) then 100 else 10

            let ceiling = choose(n -> n > 0, 1)
            """;

    @Test
    void aForkAValueHandsItsRuleToIsSettledInAModuleWithNoBehavior() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        String module = compilation.modules().get(0);
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(module)).value();

        List<CoverageSites.GuardRef> guards = checked.plan().guards();

        assertFalse(guards.isEmpty(), "the value's own fork is a place to be counted at");
        assertTrue(guards.stream().allMatch(guard -> guard.decided().isSettled()),
                "and it is known which rule decides it: " + guards);
    }
}
