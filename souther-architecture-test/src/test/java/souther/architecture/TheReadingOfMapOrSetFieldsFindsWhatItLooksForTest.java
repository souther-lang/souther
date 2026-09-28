package souther.architecture;

import org.junit.jupiter.api.Test;
import souther.compiler.carrier.Lookup;
import souther.compiler.carrier.Membership;

import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@link MapOrSetFields} finds a field typed as a map or a set, and passes over one that is not.
 *
 * <p>The mechanism every rule about one carrier's fields reads through, so the controls are here and
 * not repeated beside each of those rules: a rule that passed because this had stopped looking would
 * read as every carrier being clean. Asked of what was compiled beside this test, not of what the
 * repository publishes — which is exactly what those rules say holds none of these.
 */
class TheReadingOfMapOrSetFieldsFindsWhatItLooksForTest {

    private static final CompiledOutputs AND_WHAT_IS_COMPILED_BESIDE_IT =
            CompiledOutputs.ofEverythingCompiledHere();

    private static final String HOLDING =
            "souther/architecture/TheReadingOfMapOrSetFieldsFindsWhatItLooksForTest$AClassHoldingOne";

    private static final String NOT_HOLDING =
            "souther/architecture/TheReadingOfMapOrSetFieldsFindsWhatItLooksForTest"
                    + "$AClassHoldingNeither";

    /**
     * The positive control, one field to each way a map or a set is typed: through the interface,
     * and as a platform implementation this does not name by hand, so that catching the second is
     * not an accident of the first.
     */
    @Test
    void aFieldTypedAsAMapOrASetIsFoundHoweverItIsTyped() {
        List<String> found = MapOrSetFields.in(AND_WHAT_IS_COMPILED_BESIDE_IT.read(HOLDING));

        assertTrue(found.contains(HOLDING + "#throughTheMapInterface Ljava/util/Map;"),
                "a field typed through java.util.Map was not found: " + found);
        assertTrue(found.contains(HOLDING + "#throughTheSetInterface Ljava/util/Set;"),
                "a field typed through java.util.Set was not found: " + found);
        assertTrue(found.contains(HOLDING
                        + "#throughAnImplementation Ljava/util/concurrent/ConcurrentHashMap;"),
                "a field typed as a platform implementation this rule does not name by hand was"
                        + " not found, so what it looks for is a name on a list rather than what"
                        + " the field's type is: " + found);
    }

    /**
     * The negative control. What a carrier is moved to must read as clean, or a rule about it could
     * never pass and would be red for a reason that has nothing to do with a regression.
     */
    @Test
    void aFieldTypedAsALookupOrAMembershipIsPassedOver() {
        assertEquals(List.of(), MapOrSetFields.in(AND_WHAT_IS_COMPILED_BESIDE_IT.read(NOT_HOLDING)));
    }

    /** A class written to hold a map and a set, for the positive control above. Nothing calls it and
     *  nothing may. */
    static final class AClassHoldingOne {

        /** Read by the rule above and by nothing here: a field it finds is the whole of what this
         *  stands for. */
        @SuppressWarnings("UnusedVariable")
        private final Map<String, Integer> throughTheMapInterface = Map.of();

        /** As above. */
        @SuppressWarnings("UnusedVariable")
        private final Set<String> throughTheSetInterface = Set.of();

        /** As above. */
        @SuppressWarnings("UnusedVariable")
        private final ConcurrentHashMap<String, Integer> throughAnImplementation =
                new ConcurrentHashMap<>();

        private AClassHoldingOne() {
        }
    }

    /** A class written to hold what a map and a set are moved to, for the negative control. */
    static final class AClassHoldingNeither {

        /** Read by the rule above and by nothing here. */
        @SuppressWarnings("UnusedVariable")
        private final Lookup<String, Integer> asALookup = Lookup.built(_ -> { });

        /** As above. */
        @SuppressWarnings("UnusedVariable")
        private final Membership<String> asAMembership = Membership.built(_ -> { });

        private AClassHoldingNeither() {
        }
    }
}
