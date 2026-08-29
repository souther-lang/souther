package souther.compiler.examples;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Constructor;
import java.lang.reflect.Modifier;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * An arm carrying something derived from something else it carries is made only where the two are
 * written together.
 *
 * <p>{@link ContractObservation.Broken} holds what was answered twice: structurally, and written the
 * way a fixture writes a value. The second is a rendering of the first, and only the place that made
 * them has what relates the two — the module's declarations, which are what tell a newtype from what
 * it wraps. A canonical constructor says that any combination of components is a value, which is
 * true of independent observations and false of these: it would admit an answer of seven beside a
 * text reading {@code TodoId(99)}, and put the rendering inside {@code equals}, so writing a value
 * differently would make it a different observation.
 *
 * <p>{@link ContractObservation.NoClauseWasBroken} is closed for its own reason — what clauses bore
 * on the answer is evidence it is to gain, and a constructor callers write is one a later component
 * breaks.
 *
 * <p>Measured against the shape of the API rather than against an answer. Both reasons are written
 * down where the arms are, and a sentence is kept by whoever reads it; a constructor is kept by
 * everyone.
 */
class AnObservationIsOnlyEverMadeByWhatObservedItTest {

    /** The arms nothing outside this package may make, and why each is one. */
    private static final List<Class<?>> CLOSED = List.of(
            ContractObservation.NoClauseWasBroken.class,
            ContractObservation.Broken.class);

    @Test
    void aClosedArmHasNoConstructorAReaderCanReach() {
        List<String> reachable = new ArrayList<>();
        for (Class<?> arm : CLOSED) {
            for (Constructor<?> c : arm.getDeclaredConstructors()) {
                if (Modifier.isPublic(c.getModifiers()) || Modifier.isProtected(c.getModifiers())) {
                    reachable.add(c.toString());
                }
            }
        }
        assertEquals(List.of(), reachable,
                "a reader outside this package could state an observation nothing observed");
    }

    /**
     * And they are not records, which is what would give them one back.
     *
     * <p>The constructor above is what the rule is about; this says where it would come from. A
     * record written here compiles, ships a public canonical constructor, and reads as a tidying-up
     * of an arm that looks like data — so the reason is written down beside the check.
     */
    @Test
    void aClosedArmIsNotARecord() {
        List<String> records = new ArrayList<>();
        for (Class<?> arm : CLOSED) {
            if (arm.isRecord()) {
                records.add(arm.getName());
            }
        }
        assertEquals(List.of(), records,
                "a record's canonical constructor is public, and its equality is over every"
                        + " component — including one that is a rendering of another");
    }

    /**
     * The arms whose components are independent stay records, and this says which those are.
     *
     * <p>Without it the rule above reads as "observations are classes", and the next arm added would
     * be closed for no reason. What decides is whether one component is derived from another.
     */
    @Test
    void anArmOfIndependentComponentsIsARecord() {
        List<String> notRecords = new ArrayList<>();
        for (Class<?> arm : List.of(ContractObservation.NothingStated.class,
                ContractObservation.Unobserved.class)) {
            if (!arm.isRecord()) {
                notRecords.add(arm.getName());
            }
        }
        assertEquals(List.of(), notRecords,
                "nothing these carry is worked out from anything else they carry");
    }

    /** Every arm is one of the two, so an arm added later is classified rather than defaulted. */
    @Test
    void everyArmIsClassifiedOneWayOrTheOther() {
        List<String> unclassified = new ArrayList<>();
        for (Class<?> arm : ContractObservation.class.getPermittedSubclasses()) {
            boolean closed = CLOSED.contains(arm);
            if (closed == arm.isRecord()) {
                unclassified.add(arm.getName());
            }
        }
        assertEquals(List.of(), unclassified,
                "an arm is a record whose components are independent, or a class this package makes");
    }
}
