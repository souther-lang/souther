package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Granularity;
import souther.compiler.numeric.Rel;
import souther.compiler.types.ValueName;

import java.util.List;
import java.util.Map;
import java.util.stream.IntStream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A comparison of the number an operation answering the order of its arguments answered states, of
 * those arguments, what the answers it can give say.
 *
 * <p>Held against the answers each such operation gives, written down here and not asked of the
 * domain the reading composes in: a comparison stands exactly for an order where it holds on the
 * answers on that side of nought and on no other, and is settled where it holds on all of them or
 * none. Every relation and every number from a few below nought to a few above; and a sign, three
 * answers, holds on a set of them that is always one of the six relations or none or all.
 */
class WhatASignOfAnOrderStatesOfItsArgumentsTest {

    private static final List<Integer> A_SIGN = List.of(-1, 0, 1);

    /** What each operation can answer, as far as this reaches: a sign, or any count of days. */
    private static final Map<ValueName, List<Integer>> ANSWERS = Map.of(
            new ValueName.Stdlib.Operation("Int", "compare"), A_SIGN,
            new ValueName.Stdlib.Operation("Decimal", "compare"), A_SIGN,
            new ValueName.Stdlib.Operation("Rational", "compare"), A_SIGN,
            new ValueName.Stdlib.Operation("Date", "daysBetween"),
            IntStream.rangeClosed(-6, 6).boxed().toList());

    @Test
    void theOperationsAnsweringAnOrderAreTheOnesWrittenDownHere() {
        assertEquals(ANSWERS.keySet(),
                DefaultBoundOperationFacts.get().statesTheOrderOfItsArguments(),
                "an operation answering an order that is not written down here is not held to it");
    }

    @Test
    void aComparisonOfTheSignStatesWhatTheAnswersOnEachSideOfNoughtSay() {
        int exact = 0;
        for (Map.Entry<ValueName, List<Integer>> each : ANSWERS.entrySet()) {
            for (Rel rel : Rel.values()) {
                for (int against = -3; against <= 3; against++) {
                    int at = against;
                    TheSignOfAnOrder.Stands stands = TheSignOfAnOrder.of(each.getKey(),
                            Granularity.DISCRETE, rel, ExactRatio.of(against));
                    String asked = each.getKey() + " " + rel + " " + against;
                    List<Integer> answers = each.getValue();
                    if (answers.equals(A_SIGN)) {
                        assertTrue(stands instanceof TheSignOfAnOrder.Stands.Settled
                                        || (stands instanceof TheSignOfAnOrder.Stands.Between(
                                                Rel _, boolean exactly) && exactly),
                                () -> asked + " holds on a set of three answers, which is an"
                                        + " order of the arguments or none: " + stands);
                    }
                    switch (stands) {
                        case null -> assertTrue(answers.stream().anyMatch(v -> rel.holds(
                                        Integer.signum(v - at)))
                                        && answers.stream().anyMatch(v -> !rel.holds(
                                                Integer.signum(v - at))),
                                () -> asked + " is left open only where it is neither always"
                                        + " nor never so");
                        case TheSignOfAnOrder.Stands.Settled(boolean holds) -> {
                            for (int v : answers) {
                                assertEquals(holds, rel.holds(Integer.signum(v - at)),
                                        () -> asked + " is settled whatever is answered");
                            }
                        }
                        case TheSignOfAnOrder.Stands.Between(Rel between, boolean exactly) -> {
                            for (int v : answers) {
                                boolean holds = rel.holds(Integer.signum(v - at));
                                boolean ordered = between.holds(Integer.signum(v));
                                assertTrue(!holds || ordered, () -> asked + " proves the"
                                        + " arguments stand " + between + " at answer " + v);
                                if (exactly) {
                                    assertEquals(ordered, holds, () -> asked + " is exactly"
                                            + " the arguments standing " + between
                                            + ", and is not at answer " + v);
                                }
                            }
                            if (exactly) {
                                exact++;
                            }
                        }
                    }
                }
            }
        }
        assertTrue(exact > 0, "some comparison is exactly an order of the arguments");
    }

    /** A count of days held above one proves the later date is later, and is not where it is. */
    @Test
    void aCountHeldPastNoughtProvesAnOrderWithoutBeingIt() {
        TheSignOfAnOrder.Stands stands = TheSignOfAnOrder.of(
                new ValueName.Stdlib.Operation("Date", "daysBetween"), Granularity.DISCRETE,
                Rel.GT, ExactRatio.of(1));
        assertEquals(new TheSignOfAnOrder.Stands.Between(Rel.GT, false), stands);
    }
}
