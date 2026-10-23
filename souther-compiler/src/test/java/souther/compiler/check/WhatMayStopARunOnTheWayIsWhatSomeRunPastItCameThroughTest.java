package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Answer;
import souther.compiler.query.Compilation;
import souther.compiler.reach.WhatMayStopARun;
import souther.compiler.types.SourceConstruct;

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
        Answer<Map<String, PathReachability.Answers.AsRun>> arrived =
                compilation.db().ask(new Adequacy.Arrived("w1"));
        Set<WhatMayStopARun> out = new LinkedHashSet<>();
        arrived.value().values().forEach(asRun -> asRun.answers().arrivals().stopsBefore()
                .values().forEach(out::addAll));
        return out;
    }

    /** What is filed as what may stop a run on the way to the comparison {@code lines} write
     *  first, in every copy of it. */
    private static Set<WhatMayStopARun> stopsBeforeTheFirst(String lines) {
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
        Answer<Map<String, PathReachability.Answers.AsRun>> arrived =
                compilation.db().ask(new Adequacy.Arrived("w1"));
        Set<WhatMayStopARun> out = new LinkedHashSet<>();
        arrived.value().values().forEach(asRun -> asRun.answers().arrivals().stopsBefore()
                .forEach((at, stops) -> {
                    if (at.origin().ordinal() == 1
                            && at.origin().kind() == SourceConstruct.BINARY) {
                        out.addAll(stops);
                    }
                }));
        return out;
    }

    /**
     * A comparison reading where the element stands, or what a walk carried from the element
     * before, is reached past the first element only by a run that got through the whole step at
     * every element before it: after the comparison, and in an arm it does not take, as well as
     * before it. Whatever there answers on some runs only is that application, to the comparison.
     * One reading the element alone is reached on a list of that one element, past nothing.
     */
    @Test
    void whatTheStepWorksOutIsOnTheWayToAComparisonOfWhatTheApplicationsBeforeMade() {
        assertEquals(Set.of(new WhatMayStopARun.ACall()), stopsBeforeTheFirst("""
                    let c = List.mapIndexed((i, x) -> (if i == n then 1 else 0) + x * a, xs)"""));
        assertEquals(Set.of(new WhatMayStopARun.ACall()), stopsBeforeTheFirst("""
                    let c = List.mapIndexed((i, x) -> { let j = i
                        (if j == n then 1 else 0) + x * a }, xs)"""),
                "a name the step binds to the position is the position");
        assertEquals(Set.of(new WhatMayStopARun.ACall()), stopsBeforeTheFirst("""
                    let c = List.fold((w, x) -> if x > w then { let z = x * a
                            x } else w, 0, xs)"""));
        assertEquals(Set.of(), stopsBeforeTheFirst("""
                    let c = List.mapIndexed((i, x) -> (if x == n then 1 else 0) + x * a, xs)"""));
        assertEquals(Set.of(), stopsBeforeTheFirst("""
                    let c = List.fold((w, x) -> if x > w then x else w, 0, xs)"""),
                "a step nothing in which may stop a run");
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
