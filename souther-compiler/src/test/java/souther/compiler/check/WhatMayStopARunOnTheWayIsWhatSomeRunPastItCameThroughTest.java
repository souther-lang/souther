package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Answer;
import souther.compiler.query.Compilation;
import souther.compiler.reach.WhatMayStopARun;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What may stop a run on the way to a comparison, for what nothing here says, is what some run
 * getting there came through.
 *
 * <p>{@code a * n} over two values nothing bounds answers where their product fits an {@code Int},
 * which no form here says, so a run past it may have stopped there; {@code a + 1} answers where it
 * fits, which is read. A fork's ways are what a run past it came through only where some run leaves
 * by them: a way that answers nothing is no way to anywhere past the fork, and what may have stopped
 * a run on it says nothing of a run that got there. And a closure's body is worked out by the call
 * that applies it, so whatever in it answers on some runs only is that call, to whatever follows.
 */
class WhatMayStopARunOnTheWayIsWhatSomeRunPastItCameThroughTest {

    private static final String GREATEST = "9223372036854775807";

    /** Every kind of thing filed as one that may stop a run on the way to a comparison. */
    private static Set<WhatMayStopARun> stopsBefore(String lines) {
        Compilation compilation = Compilation.ofSource("""
                module w1

                data Ok
                data No
                data Answer = Ok | No

                behavior f : (xs: List<Int>, a: Int, n: Int, b: Int) -> Answer
                let f (xs, a, n, b) = {
                %s
                    guard b > 3 else No
                    Ok
                }
                """.formatted(lines), "Main");
        compilation.answerEverything();
        Answer<Map<String, PathReachability.Answers.AsRun>> arrived =
                compilation.db().ask(new Adequacy.Arrived("w1"));
        Set<WhatMayStopARun> out = new LinkedHashSet<>();
        arrived.value().values().forEach(asRun -> asRun.answers().arrivals().stopsBefore()
                .values().forEach(out::addAll));
        return out;
    }

    @Test
    void aProductNothingBoundsMayStopARunAndASumDoesNot() {
        assertEquals(Set.of(new WhatMayStopARun.AnOperator()),
                stopsBefore("    let c = a * n"));
        assertEquals(Set.of(), stopsBefore("    let c = a + 1"));
    }

    @Test
    void aWayOutOfAForkSomeRunLeavesByCarriesWhatMayStopOnIt() {
        assertEquals(Set.of(new WhatMayStopARun.AnOperator()),
                stopsBefore("    let c = if b > 0 then a * n else 0"));
    }

    /** The product is on a way that then answers nothing, so no run past the fork came by it. */
    @Test
    void aWayOutOfAForkNoRunLeavesByCarriesNothing() {
        assertEquals(Set.of(), stopsBefore("""
                    guard a == %s else No
                    let c = if b > 0 then (a * n) + (a + 1) else 0""".formatted(GREATEST)));
        assertEquals(Set.of(new WhatMayStopARun.AnOperator()), stopsBefore("""
                    guard a == %s else No
                    let c = if b > 0 then (a * n) + (a - 1) else 0""".formatted(GREATEST)),
                "the same way answering, which a run past the fork may come by");
    }

    @Test
    void whatAClosureWorksOutIsTheCallThatAppliesIt() {
        assertEquals(Set.of(new WhatMayStopARun.ACall()),
                stopsBefore("    let c = List.sortBy(x -> x * n, xs)"));
        assertEquals(Set.of(new WhatMayStopARun.ACall()),
                stopsBefore("    let c = List.sortBy(x -> x + 1, xs)"),
                "a sum in it is read where it is worked out, and nothing past the call holds"
                        + " where each application got past it");
        assertEquals(Set.of(), stopsBefore("    let c = List.sortBy(x -> x, xs)"),
                "the kernel applying it ends no run itself");
    }

    /** What stops a run past a quotient is read where the divisor is a form. */
    @Test
    void aQuotientIsReadWhereItsDivisorIsAForm() {
        assertEquals(Set.of(), stopsBefore("    let c = 10 / n"));
        assertEquals(List.of(new WhatMayStopARun.AnOperator()),
                List.copyOf(stopsBefore("    let c = 10 / (a * n)")));
    }
}
