package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What the operators of a reading and a candidate under trial hold is held in counted parts
 * ({@link Tallied}), so that no change to them leaves their mark where it was.
 *
 * <p>A mark that a hand moves on each change is a mark that a change added without the hand
 * leaves behind, and a reading kept under the old mark is taken where it would not be the same. A
 * field of one of these that is neither a counted part nor in the mark as it is
 * ({@link Tallied.InTheMark}) is that change.
 */
class EveryChangeToWhatAMarkSaysIsCountedTest {

    private static final Set<Class<?>> COUNTED = Set.of(Tallied.Changes.class,
            Tallied.Value.class, Tallied.Group.class, Tallied.Sequence.class, Tallied.Table.class);

    @Test
    void everyFieldOfWhatSaysWhatItHasBeenToldIsCountedOrInTheMark() {
        Set<String> neither = new TreeSet<>();
        for (Class<?> owner : List.of(Operators.class, Pullback.Trial.class)) {
            for (Field each : owner.getDeclaredFields()) {
                if (Modifier.isStatic(each.getModifiers()) || each.isSynthetic()) {
                    continue;
                }
                boolean counted = COUNTED.contains(each.getType())
                        && Modifier.isFinal(each.getModifiers());
                if (!counted && !each.isAnnotationPresent(Tallied.InTheMark.class)) {
                    neither.add(owner.getSimpleName() + "." + each.getName());
                }
            }
        }

        assertEquals(Set.of(), neither, "a field whose change the mark would not see");
    }
}
