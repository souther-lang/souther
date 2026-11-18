package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.partition.ReadingState.NoPartOfAReading;
import souther.compiler.partition.ReadingState.NoPartOfAReading.Why;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.EnumSet;
import java.util.HashSet;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every field of a {@link Pullback} is a part of the state of its readings, which says what a
 * reading kept to be taken again does with it, or says why it is none ({@link NoPartOfAReading}).
 *
 * <p>A reading made at one place is taken at another only if everything it depends on stands the
 * same and everything it would have added is still there. A field added to the class that is
 * neither is a piece of state that a reading may depend on or change, and nothing says which.
 */
class EveryFieldOfAPullbackIsAPartOfItsStateOrSaysWhyNotTest {

    private static Set<Field> fieldsOfAPullback() {
        Set<Field> out = new HashSet<>();
        for (Field each : Pullback.class.getDeclaredFields()) {
            if (!Modifier.isStatic(each.getModifiers()) && !each.isSynthetic()) {
                out.add(each);
            }
        }
        return out;
    }

    private static boolean isAPart(Field field) {
        return ReadingState.Part.class.isAssignableFrom(field.getType());
    }

    @Test
    void everyFieldIsAPartOrSaysWhyItIsNone() {
        Set<String> neither = new TreeSet<>();
        Set<String> both = new TreeSet<>();
        for (Field each : fieldsOfAPullback()) {
            boolean saysWhy = each.isAnnotationPresent(NoPartOfAReading.class);
            if (isAPart(each) == saysWhy) {
                (saysWhy ? both : neither).add(each.getName());
            }
        }

        assertEquals(Set.of(), neither, "a field that is no part and says nothing of why");
        assertEquals(Set.of(), both, "a part that says it is none");
    }

    @Test
    void aPartIsTheSamePartForAsLongAsTheReaderIs() {
        for (Field each : fieldsOfAPullback()) {
            if (isAPart(each)) {
                assertTrue(Modifier.isFinal(each.getModifiers()),
                        each.getName() + " is a part and is assigned: a reading kept would be "
                                + "compared on the part it was made with");
            }
        }
    }

    @Test
    void aFieldThatStaysTheSameOrOnlyHoldsWhatWasKeptCannotBeOneThatIsAssigned() {
        Set<Why> hold = EnumSet.of(Why.FIXED, Why.LEDGER, Why.CACHE, Why.ACCRUES, Why.MEMO,
                Why.STATE);
        for (Field each : fieldsOfAPullback()) {
            NoPartOfAReading why = each.getAnnotation(NoPartOfAReading.class);
            if (why != null && hold.contains(why.value())) {
                assertTrue(Modifier.isFinal(each.getModifiers()),
                        each.getName() + " is " + why.value() + " and is assigned");
            }
        }
    }

}
