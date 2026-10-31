package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Field;
import java.lang.reflect.Modifier;
import java.util.EnumSet;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Every field of a {@link Pullback} says what a reading kept to be taken again does with it, and
 * says it in the table ({@link ReadingRoles}) and nowhere else.
 *
 * <p>A reading made at one place is taken at another only if everything it depends on stands the
 * same and everything it would have added is still there. A field added to the class with no role
 * is a piece of state that a reading may depend on or change, and nothing says which.
 */
class EveryFieldOfAPullbackSaysWhatAReadingKeptToBeTakenAgainDoesWithItTest {

    private static Set<String> fieldsOfAPullback() {
        Set<String> out = new TreeSet<>();
        for (Field each : Pullback.class.getDeclaredFields()) {
            if (!Modifier.isStatic(each.getModifiers()) && !each.isSynthetic()) {
                out.add(each.getName());
            }
        }
        return out;
    }

    @Test
    void theTableNamesTheFieldsOfAPullbackAndNoOthers() {
        assertEquals(fieldsOfAPullback(), new TreeSet<>(ReadingRoles.OF_A_PULLBACK.keySet()),
                "a field with no role, or a role for a field that is gone");
    }

    @Test
    void aFieldThatStaysTheSameOrOnlyHoldsWhatWasKeptCannotBeOneThatIsAssigned() {
        Set<ReadingRole> hold = EnumSet.of(ReadingRole.FIXED, ReadingRole.LEDGER, ReadingRole.CACHE,
                ReadingRole.ACCRUES, ReadingRole.MEMO);
        for (Field each : Pullback.class.getDeclaredFields()) {
            ReadingRole role = ReadingRoles.OF_A_PULLBACK.get(each.getName());
            if (role != null && hold.contains(role)) {
                assertTrue(Modifier.isFinal(each.getModifiers()),
                        each.getName() + " is " + role + " and is assigned");
            }
        }
    }

    @Test
    void everyRoleIsGivenToSomeField() {
        Set<ReadingRole> given = EnumSet.noneOf(ReadingRole.class);
        given.addAll(ReadingRoles.OF_A_PULLBACK.values());

        assertEquals(EnumSet.allOf(ReadingRole.class), given, "a role that no field has");
    }

    @Test
    void thePullbackMakesItsStateFromTheTable() {
        // Made once for the class; a field with no role would stop it from being made at all.
        new ReadingState(Pullback.class, ReadingRoles.OF_A_PULLBACK);
    }
}
