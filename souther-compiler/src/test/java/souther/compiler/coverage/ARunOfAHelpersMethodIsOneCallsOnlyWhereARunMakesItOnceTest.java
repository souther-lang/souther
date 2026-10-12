package souther.compiler.coverage;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.ValueName;

import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A run recorded in the method of a helper that calls itself is one call's only where a run of the
 * behavior makes that call once: one call written, in the behavior's own body, at a place one run
 * passes once.
 *
 * <p>Written once is not made once. A call inside a closure is one node and is made once for each
 * element the closure is applied to, and a run recorded in the helper's method is any of those.
 */
class ARunOfAHelpersMethodIsOneCallsOnlyWhereARunMakesItOnceTest {

    private static final String MODEL = """
            module probe

            data Low
            data High

            partial let go (xs: List<Int>): List<Int> =
                match List.get(0, xs) with
                    | None -> []
                    | Some x -> if x > 0 then [ x ] else go(List.drop(1, xs))

            behavior pick : (xs: List<Int>, ys: List<Int>, xss: List<List<Int>>) -> Low | High
            let pick (xs, ys, xss) = if GUARD then High else Low
            """;

    private static final ValueName.Helper GO = new ValueName.Helper("probe", "go");

    @Test
    void oneCallInTheBodyIsMadeOnce() {
        assertTrue(runsOnce("List.length(go(xs)) >= 1"));
    }

    @Test
    void twoCallsAreNot() {
        assertFalse(runsOnce("List.length(go(xs)) + List.length(go(ys)) >= 1"));
    }

    @Test
    void oneCallInsideAClosureIsMadeOnceForEachElement() {
        assertFalse(runsOnce("List.any(zs -> List.length(go(zs)) >= 1, xss)"));
    }

    private static boolean runsOnce(String guard) {
        Compilation compilation = Compilation.ofSource(MODEL.replace("GUARD", guard), "Main");
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked("probe")).value();
        assertNotNull(checked, "the model under test compiles");
        RunBodies run = checked.run("pick");
        return checked.plan().runsOnce(GO, run.entry());
    }
}
