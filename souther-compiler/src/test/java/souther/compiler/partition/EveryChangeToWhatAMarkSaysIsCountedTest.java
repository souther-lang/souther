package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.Collections;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What the operators of a reading and a candidate under trial hold is held in counted parts
 * ({@link Tallied}) of their own counts, so that no change to them leaves their mark where it was.
 *
 * <p>A mark that a hand moves on each change is a mark that a change added without the hand
 * leaves behind, and a reading kept under the old mark is taken where it would not be the same. A
 * field of one of these that is neither a counted part nor in the mark as it is
 * ({@link Tallied.InTheMark}) is that change, and so is a counted part of a count the mark does not
 * read.
 */
class EveryChangeToWhatAMarkSaysIsCountedTest {

    private static final List<Object> OWNERS = List.of(new Operators(), new Pullback.Trial());

    private static List<Field> fieldsOf(Object owner) {
        return List.of(owner.getClass().getDeclaredFields()).stream()
                .filter(each -> !Modifier.isStatic(each.getModifiers()) && !each.isSynthetic())
                .toList();
    }

    private static Object read(Field field, Object owner) {
        try {
            field.setAccessible(true);
            return field.get(owner);
        } catch (IllegalAccessException e) {
            throw new IllegalStateException(field.getName(), e);
        }
    }

    @Test
    void everyFieldOfWhatSaysWhatItHasBeenToldIsCountedOrInTheMark() {
        Set<String> neither = new TreeSet<>();
        for (Object owner : OWNERS) {
            for (Field each : fieldsOf(owner)) {
                boolean counted = (Tallied.Part.class.isAssignableFrom(each.getType())
                        || each.getType() == Tallied.Changes.class)
                        && Modifier.isFinal(each.getModifiers());
                if (!counted && !each.isAnnotationPresent(Tallied.InTheMark.class)) {
                    neither.add(owner.getClass().getSimpleName() + "." + each.getName());
                }
            }
        }

        assertEquals(Set.of(), neither, "a field whose change the mark would not see");
    }

    @Test
    void everyCountedPartCountsIntoACountOfItsOwner() {
        Set<String> elsewhere = new TreeSet<>();
        for (Object owner : OWNERS) {
            Set<Tallied.Changes> own = Collections.newSetFromMap(new IdentityHashMap<>());
            for (Field each : fieldsOf(owner)) {
                if (read(each, owner) instanceof Tallied.Changes changes) {
                    own.add(changes);
                }
            }
            for (Field each : fieldsOf(owner)) {
                if (read(each, owner) instanceof Tallied.Part part
                        && !own.contains(part.changes())) {
                    elsewhere.add(owner.getClass().getSimpleName() + "." + each.getName());
                }
            }
        }

        assertEquals(Set.of(), elsewhere, "a part whose changes its owner's mark does not count");
    }
}
