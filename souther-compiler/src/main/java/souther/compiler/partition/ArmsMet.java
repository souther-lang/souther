package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.inputs.InputReading;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;

/**
 * The arm of a {@code match} each condition that entered one is, kept with the reading of the input.
 *
 * <p>A condition's name is an opaque number of the reading that met it, so it says nothing of which
 * arm it is. The reading that names it is the one place that knows, and a reader asking whether a
 * condition left out of a way is the arm of one particular match asks here, by the arm itself.
 */
final class ArmsMet {

    private final Map<ConditionOccurrence, Core.Case> byCondition = new ConcurrentHashMap<>();

    /** What is kept for the reading {@code read}. */
    static ArmsMet of(InputReading read) {
        return read.derived(ArmsMet.class, _ -> new ArmsMet());
    }

    /** Files {@code arm} as what the condition {@code met} is. */
    void met(ConditionOccurrence met, Core.Case arm) {
        byCondition.put(met, arm);
    }

    /** Whether the condition {@code met} is the arm {@code arm} itself. */
    boolean isTheArm(ConditionOccurrence met, Core.Case arm) {
        return byCondition.get(met) == arm;
    }
}
