package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.collect.AppendOnly;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.OrderedInterval;
import souther.compiler.numeric.OrderedIntervals;
import souther.compiler.numeric.Rel;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Whether a state reaches nothing is what {@link Known#reachesNothing} answers, kept or not, and
 * however often it is asked: what an engine keeps changes how often the answer is worked out and
 * never what it is.
 *
 * <p>Asked over a state each domain leaves nothing in and one nothing is said of, so that an
 * answer of either kind is one this keeps, and each asked twice of the same table, the second time
 * answered from what the first left.
 */
class AReachabilityKeptIsTheReachabilityAskedTest {

    private static final FactSubject A_POSITION =
            FactSubject.of(new Term.Interner().written("some position"));

    @Test
    void eachStateIsAnsweredAsItIsAskedWhetherTheAnswerIsKeptOrNot() {
        ReachabilityAnswers kept = ReachabilityAnswers.kept();
        for (ConstraintState<FactSubject> state : List.of(
                ConstraintState.top(FactSubject.inOneOrder()), numbersAtBottom(),
                orderedAtBottom())) {
            Known known = reaching(state);
            boolean asked = known.reachesNothing();
            assertEquals(asked, kept.reachesNothing(known), () -> "kept, first asked: " + state);
            assertEquals(asked, kept.reachesNothing(known), () -> "kept, asked again: " + state);
            assertEquals(asked, ReachabilityAnswers.NONE.reachesNothing(known),
                    () -> "not kept: " + state);
        }
    }

    /** Each of the two kinds of answer is among those asked, so a table answering one alone is
     *  not one this passes. */
    @Test
    void theStatesAskedReachSomethingAndReachNothing() {
        assertEquals(List.of(false, true, true), List.of(
                reaching(ConstraintState.top(FactSubject.inOneOrder())).reachesNothing(),
                reaching(numbersAtBottom()).reachesNothing(),
                reaching(orderedAtBottom()).reachesNothing()));
    }

    private static Known reaching(ConstraintState<FactSubject> constraints) {
        return new Known(constraints, List.of(), AppendOnly.empty(),
                new Known.Unguarded(ConstraintState.top(FactSubject.inOneOrder())), Map.of(),
                Known.Choices.NONE);
    }

    private static ConstraintState<FactSubject> numbersAtBottom() {
        return ConstraintState.top(FactSubject.inOneOrder())
                .taking(LinearForm.constant(ExactRatio.ONE), Rel.LE, Map.of());
    }

    private static ConstraintState<FactSubject> orderedAtBottom() {
        return ConstraintState.top(FactSubject.inOneOrder())
                .taking(OrderedIntervals.at(A_POSITION,
                        new OrderedInterval(Endpoint.inclusive(Count.of(6)), null)), Map.of())
                .taking(OrderedIntervals.at(A_POSITION,
                        new OrderedInterval(null, Endpoint.inclusive(Count.of(2)))), Map.of());
    }
}
