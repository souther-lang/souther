package souther.compiler.examples;

import org.junit.jupiter.api.Test;
import souther.compiler.evaluate.EvaluationContext;
import souther.compiler.evaluate.StepLimitExceeded;

import java.lang.reflect.InvocationTargetException;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the compiler goes over of a value an evaluation built is counted, all of it, and what stopped
 * the evaluation is told apart from a failure however it arrives.
 */
class AWalkOverWhatAnEvaluationHoldsIsCountedTest {

    private static final int DEEP = 300;
    private static final int WIDE = 5_000;

    /** A list of {@code WIDE} numbers under {@code DEEP} lists, each holding the next: deeper than a
     *  report's observation goes. */
    private static List<Object> deepAndWide() {
        List<Object> bottom = new ArrayList<>();
        for (long i = 0; i < WIDE; i++) {
            bottom.add(i);
        }
        Object value = bottom;
        for (int i = 0; i < DEEP; i++) {
            value = List.of(value);
        }
        return List.of(value);
    }

    /** A value about to be written out is paid for to its last node, below the depth a report stops
     *  showing it at. */
    @Test
    void whatIsPaidForBeforeAValueIsWrittenIsAllOfIt() {
        EvaluationContext.begin(Long.MAX_VALUE / 2, 100);
        try {
            PaidForBeforeItIsWalked.payFor(deepAndWide());
            long spent = EvaluationContext.spent(Long.MAX_VALUE / 2);
            long nodes = (long) DEEP + WIDE;
            assertTrue(spent >= nodes, "a value of " + nodes + " nodes cost " + spent);
        } finally {
            EvaluationContext.end();
        }
    }

    /** And it stops the evaluation part of the way through where the budget runs out. */
    @Test
    void whatIsPaidForStopsWhereTheBudgetRunsOut() {
        EvaluationContext.begin(1_000, 100);
        try {
            assertThrows(StepLimitExceeded.class, () -> PaidForBeforeItIsWalked.payFor(deepAndWide()));
        } finally {
            EvaluationContext.end();
        }
    }

    /** A stop thrown inside code reached reflectively arrives wrapped, and is found inside. */
    @Test
    void aStopIsFoundInsideWhatWrapsIt() throws NoSuchMethodException {
        Runnable stopping = () -> {
            throw StepLimitExceeded.INSTANCE;
        };
        InvocationTargetException wrapped = assertThrows(InvocationTargetException.class,
                () -> Runnable.class.getMethod("run").invoke(stopping));
        assertSame(StepLimitExceeded.INSTANCE, EvaluationContext.overspent(wrapped));
        assertSame(StepLimitExceeded.INSTANCE,
                EvaluationContext.overspent(new IllegalStateException("reported", wrapped)));
        assertNull(EvaluationContext.overspent(new IllegalStateException("not a stop")));
    }
}
