package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Constructor;
import java.lang.reflect.Modifier;
import java.util.Arrays;

import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a measurement hands a reader is made by the measurement and by nothing else.
 *
 * <p>The one thing this package holds to by a check rather than by construction. Every other way a
 * walk could be paired with geometry measured somewhere else is closed by what the entry points
 * take: a reader outside {@code souther.compiler.partition} cannot walk a row at all, the
 * classifier and the reader of a line take a projection rather than a walk beside a list, and a
 * projection is narrowed by what it already holds rather than by naming what to keep. All of that
 * rests on there being no second way to make one — which is a constructor's visibility, and a
 * visibility is a word somebody can widen.
 *
 * <p>So this counts the constructors. A nest may reach its own private members, so what this holds
 * is that nothing outside {@link MeasuredInput} makes one; a sibling projection making another is
 * plain in the file and is not what this is about.
 */
class AProjectionOfAMeasurementIsMadeByTheMeasurementTest {

    @Test
    void nothingOutsideTheMeasurementMakesAProjectionOfIt() {
        for (Class<?> projection : java.util.List.of(MeasuredInput.MeasuredAxes.class,
                MeasuredInput.BorderReading.class, MeasuredInput.MeasuredPosition.class)) {
            assertTrue(Arrays.stream(projection.getDeclaredConstructors())
                            .allMatch(each -> Modifier.isPrivate(each.getModifiers())),
                    () -> projection.getSimpleName() + " has a constructor outside the measurement"
                            + " can reach: " + Arrays.stream(projection.getDeclaredConstructors())
                            .map(Constructor::toString).toList());
        }
    }
}
