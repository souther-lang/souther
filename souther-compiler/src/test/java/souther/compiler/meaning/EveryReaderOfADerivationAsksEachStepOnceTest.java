package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.ReadersOfAGraph;
import souther.compiler.semantics.ConditionJoin;
import souther.test.ClosedWorldContract;

import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;
import java.util.TreeSet;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every reader of a derivation asks each step once, however many steps hold it.
 *
 * <p>A value read through a name used twice is held by two steps, so derivations are a graph, and
 * the ways down a chain of names each using the one before it twice are two to its length
 * ({@link ReadersOfAGraph}). Asked of a chain of joins and a chain of ifs, each holding the step
 * before it in every place it can.
 */
@ClosedWorldContract
class EveryReaderOfADerivationAsksEachStepOnceTest {

    /** Readers whose work is the ways down, which is what they are for. */
    private static final Map<String, String> BY_THEIR_NATURE = Map.of();

    /** How many readers are asked at least, so that finding none is not a pass. */
    private static final int AT_LEAST_ASKED = 3;

    private static Derivation joins(int length) {
        Derivation held = new Derivation.WrittenOut(true);
        for (int at = 1; at <= length; at++) {
            held = new Derivation.Joined(at % 2 == 0 ? ConditionJoin.BOTH : ConditionJoin.EITHER,
                    held, held);
        }
        return held;
    }

    private static Derivation ifs(int length) {
        Derivation held = new Derivation.WrittenOut(true);
        for (int at = 1; at <= length; at++) {
            held = new Derivation.IfThenElse(held, held, held);
        }
        return held;
    }

    @Test
    void noReaderOfADerivationGoesDownEveryWayToItsSteps() throws Exception {
        Map<Class<?>, Supplier<Object>> made = Map.of(
                Conclusion.class, () -> new Conclusion(Optional.empty()),
                Derivation.class, () -> new Derivation.WrittenOut(true));
        ReadersOfAGraph.Findings found = ReadersOfAGraph.askEach(List.of(
                new ReadersOfAGraph.Chain("joins", Derivation.class,
                        EveryReaderOfADerivationAsksEachStepOnceTest::joins, made),
                new ReadersOfAGraph.Chain("ifs", Derivation.class,
                        EveryReaderOfADerivationAsksEachStepOnceTest::ifs, made)),
                BY_THEIR_NATURE);

        assertEquals(Set.of(), found.slow(), "readers that take a growth of the ways down to "
                + "the steps on a chain of " + ReadersOfAGraph.LONG + " names as on one of "
                + ReadersOfAGraph.SHORT);
        assertTrue(found.answered().size() >= AT_LEAST_ASKED, new TreeSet<>(found.answered())
                + " answered, " + found.refused().size() + " refused, "
                + new TreeSet<>(found.notAsked()) + " not asked");
    }
}
