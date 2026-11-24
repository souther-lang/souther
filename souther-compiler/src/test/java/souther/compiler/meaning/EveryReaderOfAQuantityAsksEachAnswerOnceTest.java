package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.ReadersOfAGraph;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.ValueName;
import souther.test.ClosedWorldContract;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every reader of a quantity asks each answer once, however many answers hold it.
 *
 * <p>What an operation answers of the answer before it twice is a graph of as many values as there
 * are calls, so the ways down a chain of them are two to its length ({@link ReadersOfAGraph}). The
 * answer of an operation is the one kind of quantity that holds a quantity in two places; the
 * others hold at most one.
 */
@ClosedWorldContract
class EveryReaderOfAQuantityAsksEachAnswerOnceTest {

    private static final ValueName.Stdlib FLOOR_MOD = ValueName.Stdlib.operation("Int", "floorMod");

    /** Readers whose work is the ways down, which is what they are for. */
    private static final Map<String, String> BY_THEIR_NATURE = Map.of();

    /** How many readers are asked at least, so that finding none is not a pass. */
    private static final int AT_LEAST_ASKED = 3;

    private static DecisionAtom.OfTheInput input() {
        return new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of("i").then("x")));
    }

    private static Quantity chainOf(int length) {
        Quantity held = input();
        for (int at = 1; at <= length; at++) {
            held = new Quantity.WhatAnOperationAnswers(FLOOR_MOD, List.of(held, held));
        }
        return held;
    }

    @Test
    void noReaderOfAQuantityGoesDownEveryWayToItsAnswers() throws Exception {
        Map<Class<?>, Supplier<Object>> made = Map.of(
                Quantity.class, EveryReaderOfAQuantityAsksEachAnswerOnceTest::input);
        ReadersOfAGraph.Findings found = ReadersOfAGraph.askEach(List.of(
                new ReadersOfAGraph.Chain("answers", Quantity.class,
                        EveryReaderOfAQuantityAsksEachAnswerOnceTest::chainOf, made)),
                BY_THEIR_NATURE);

        assertEquals(Set.of(), found.slow(), "readers that take a growth of the ways down to "
                + "the answers on a chain of " + ReadersOfAGraph.LONG + " calls as on one of "
                + ReadersOfAGraph.SHORT);
        assertTrue(found.answered().size() >= AT_LEAST_ASKED, new TreeSet<>(found.answered())
                + " answered, " + found.refused().size() + " refused, "
                + new TreeSet<>(found.notAsked()) + " not asked");
    }
}
