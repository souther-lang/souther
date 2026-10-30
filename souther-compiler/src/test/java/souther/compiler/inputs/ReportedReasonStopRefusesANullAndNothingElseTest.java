package souther.compiler.inputs;

import org.junit.jupiter.api.Test;
import souther.compiler.partition.ReportedReason;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.RecordComponent;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * {@link ReportedReason.Stop} takes any combination of values and refuses a null in any component.
 *
 * <p>That is what lets it stay out of the types asked over every combination
 * ({@code TheNearestValuesOfATypeAreTheValuesEveryCombinationMakesTest}): a combination is
 * refused only for a null, so every value of a component is taken beside the first values of the
 * others and none is left to a combination further away. The product of its components' values is
 * what the nightly cannot finish, so this is asked of the two ends of each component's values —
 * the first and the last — in every combination of those ends, and not of all of them.
 *
 * <p>A finite sample: a constructor that came to tie components only at values between the ends
 * would pass it. What it holds is that a tie among the ends, or a refusal of anything but a null,
 * is named here and not found by a nightly that no longer asks.
 */
class ReportedReasonStopRefusesANullAndNothingElseTest {

    private static final RecordComponent[] COMPONENTS =
            ReportedReason.Stop.class.getRecordComponents();

    @Test
    void everyCombinationOfTheEndsOfTheValuesIsTaken() throws Exception {
        for (Object[] arguments : combinationsOfTheEnds()) {
            Object made = construct(arguments);
            assertInstanceOf(ReportedReason.Stop.class, made, Arrays.toString(arguments));
        }
    }

    /**
     * Each value a component is offered, the ones between the ends among them, beside the first
     * values of the others: a refusal of one value of a component, which the ends do not reach.
     */
    @Test
    void everyValueOfEveryComponentIsTakenBesideTheFirstValuesOfTheOthers() throws Exception {
        ValuesOfAType values = new ValuesOfAType();
        Object[] first = new Object[COMPONENTS.length];
        for (int i = 0; i < first.length; i++) {
            first[i] = values.of(COMPONENTS[i].getGenericType()).get(0);
        }
        for (int i = 0; i < first.length; i++) {
            for (Object value : values.of(COMPONENTS[i].getGenericType())) {
                Object[] arguments = first.clone();
                arguments[i] = value;
                assertInstanceOf(ReportedReason.Stop.class, construct(arguments),
                        COMPONENTS[i].getName() + " = " + value);
            }
        }
    }

    @Test
    void aNullInAnyComponentIsRefusedBesideAnyCombinationOfTheEnds() throws Exception {
        for (Object[] arguments : combinationsOfTheEnds()) {
            for (int i = 0; i < arguments.length; i++) {
                Object[] withNull = arguments.clone();
                withNull[i] = null;
                Throwable refused = assertRefused(withNull);
                assertEquals(IllegalArgumentException.class, refused.getClass(),
                        COMPONENTS[i].getName() + " null, beside " + Arrays.toString(arguments));
            }
        }
    }

    private static List<Object[]> combinationsOfTheEnds() {
        ValuesOfAType values = new ValuesOfAType();
        List<Object[]> out = new ArrayList<>();
        out.add(new Object[COMPONENTS.length]);
        for (int i = 0; i < COMPONENTS.length; i++) {
            List<Object> offered = values.of(COMPONENTS[i].getGenericType());
            List<Object> ends = List.of(offered.get(0), offered.get(offered.size() - 1));
            List<Object[]> next = new ArrayList<>();
            for (Object[] each : out) {
                for (Object end : ends) {
                    Object[] extended = each.clone();
                    extended[i] = end;
                    next.add(extended);
                }
            }
            out = next;
        }
        return out;
    }

    private static Object construct(Object[] arguments) throws Exception {
        Class<?>[] types = Arrays.stream(COMPONENTS).map(RecordComponent::getType)
                .toArray(Class<?>[]::new);
        Constructor<?> canonical = ReportedReason.Stop.class.getDeclaredConstructor(types);
        return canonical.newInstance(arguments);
    }

    private static Throwable assertRefused(Object[] arguments) throws Exception {
        try {
            construct(arguments);
        } catch (InvocationTargetException e) {
            return e.getCause();
        }
        throw new AssertionError("taken: " + Arrays.toString(arguments));
    }
}
