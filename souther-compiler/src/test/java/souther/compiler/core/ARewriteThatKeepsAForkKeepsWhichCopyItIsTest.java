package souther.compiler.core;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Bodies;
import souther.compiler.query.Compilation;
import souther.compiler.types.BindingOwner;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rewrite that keeps a fork keeps which copy of a body it stands in.
 *
 * <p>Which copy a fork is in is what says which rule the caller handed it, and it is known where the
 * expansion is elaborated and nowhere after. A Core-to-Core pass rebuilds nodes, and one that
 * rebuilt a fork without carrying this would leave a fork nothing can say the copy of — after which
 * every copy of it is counted as one arm to cover, whatever rule each was handed.
 *
 * <p>Checked over the tree the passes answer with rather than over one pass, so a pass added later
 * is held to it without this having to name it.
 */
class ARewriteThatKeepsAForkKeepsWhichCopyItIsTest {

    private static final String MODULE = "example.kept";

    private static final String MODEL = """
            module example.kept

            data Yes
            data No
            data Verdict = Yes | No
            data Count = Int

            let decide (p: (Int) -> Bool, x: Int): Verdict = if p(x) then Yes else No

            behavior twice : (a: Int, b: Int, xs: List<Int>) -> Count
                constructs Count
            let twice (a, b, xs) =
                Count((if decide(n -> n < 18, a) == Yes then 1 else 0)
                    + (if decide(m -> 18 < m, b) == Yes then 1 else 0)
                    + List.length(List.filter(k -> k > 0, xs)))

            example twice
                | "under and under" : (1, 1, [ 1 ]) -> Count(2)
            """;

    @Test
    void everyForkInACopyStillSaysWhichCopy() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.answerEverything();
        Bodies.Elaborated checked = compilation.db().ask(new Bodies.Checked(MODULE)).value();
        assertNotNull(checked, "the model under test compiles");

        Map<String, List<Core>> spliced = new LinkedHashMap<>();
        checked.behaviorBodies().forEach((behavior, body) -> {
            List<Core> found = new ArrayList<>();
            forks(body, found);
            spliced.put(behavior, found);
        });
        List<Core> forks = spliced.get("twice");
        assertNotNull(forks, "the behavior under test has a body");
        assertTrue(forks.size() >= 4,
                () -> "the model under test writes forks inside copies: " + forks.size());

        // Every fork the passes answered with that stands in a copy says which copy, and the ones
        // written where they stand say they are in none. Both are answers; what is refused is a
        // fork inside a copy that lost it on the way through.
        List<String> lost = new ArrayList<>();
        for (Core fork : forks) {
            BindingOwner within = within(fork);
            if (writtenInACopy(fork) && within == null) {
                lost.add(fork.toString());
            }
        }
        assertEquals(List.of(), lost, () -> "forks that lost which copy they are in: " + lost);
    }

    /** Whether {@code fork} came out of a body spliced into this one. */
    private static boolean writtenInACopy(Core fork) {
        return origin(fork) != null && !MODULE.equals(origin(fork).module());
    }

    private static souther.compiler.types.CoverageOrigin origin(Core fork) {
        return switch (fork) {
            case Core.If iff -> iff.origin();
            case Core.Match m -> m.origin();
            case Core.IfConstructed ic -> ic.origin();
            default -> null;
        };
    }

    private static BindingOwner within(Core fork) {
        return switch (fork) {
            case Core.If iff -> iff.expansion();
            case Core.Match m -> m.expansion();
            case Core.IfConstructed ic -> ic.expansion();
            default -> null;
        };
    }

    private static void forks(Core e, List<Core> out) {
        if (e instanceof Core.If || e instanceof Core.Match || e instanceof Core.IfConstructed) {
            out.add(e);
        }
        Core.forEachChild(e, child -> forks(child, out));
    }
}
