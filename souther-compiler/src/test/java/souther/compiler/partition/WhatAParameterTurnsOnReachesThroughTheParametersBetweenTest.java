package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The order a row's parameters are composed in, and what each of them turns on, is one answer for
 * every walk that composes a row — and what a parameter turns on reaches through the parameters
 * between: a box holding the number, and an outer list holding the box, is an outer list another
 * number may let be built.
 */
class WhatAParameterTurnsOnReachesThroughTheParametersBetweenTest {

    /** `outer` holds `box.held`, and `box` holds `n`; declared the other way round. */
    private static final ContentsAsked CHAINED = new ContentsAsked(List.of(
            new ContentsAsked.Asked(TermPath.of("outer").then("held"),
                    TermPath.of("box").then("held"), true),
            new ContentsAsked.Asked(TermPath.of("box").then("held"), TermPath.of("n"), true)));

    private static final List<String> DECLARED = List.of("outer", "box", "n");

    @Test
    void eachParameterIsComposedAfterWhatItsContainersAreHanded() {
        CompositionOrder order = ordered(CHAINED);
        assertEquals(List.of(2, 1, 0), order.order(), "n, then box, then outer");
    }

    @Test
    void whatAParameterTurnsOnReachesThroughTheOneBetween() {
        CompositionOrder order = ordered(CHAINED);
        assertEquals(Set.of("box", "n"), order.turnsOn(0), "outer turns on box, and through it n");
        assertTrue(order.mayTurnOn(0, 2), "so outer coming to nothing is a reason to try another n");
        assertTrue(order.awaited(0), "and n waits for what outer comes to");
        assertTrue(order.alone(2), "n turns on nothing");
        assertFalse(order.mayTurnOn(2, 0));
    }

    /** Two parameters each holding a value of the other are said as the parameters they are. */
    @Test
    void parametersEachHoldingTheOthersValueAreSaidInTheOrderTheyAreDeclared() {
        ContentsAsked circular = new ContentsAsked(List.of(
                new ContentsAsked.Asked(TermPath.of("b").then("xs"), TermPath.of("a").then("v"),
                        true),
                new ContentsAsked.Asked(TermPath.of("a").then("ys"), TermPath.of("b").then("w"),
                        true)));
        CompositionOrder.Result.Circular said = assertInstanceOf(
                CompositionOrder.Result.Circular.class,
                CompositionOrder.of(List.of("a", "b", "c"), circular));
        assertEquals(List.of("a", "b"), said.parameters());
    }

    private static CompositionOrder ordered(ContentsAsked contents) {
        return assertInstanceOf(CompositionOrder.Result.Ordered.class,
                CompositionOrder.of(DECLARED, contents)).order();
    }
}
