package souther.compiler.query;

import org.junit.jupiter.api.Test;

import java.lang.reflect.Method;
import java.lang.reflect.RecordComponent;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A measure a behavior is made of is one of its parts, and the record says which those are.
 *
 * <p>{@link BehaviorEvidence#parts()} is where the status, the weakening, the verdict and the
 * document all ask what a behavior was measured by. It is a list written by hand, and what holds it
 * to the behavior it is a list of was a sentence in its documentation saying to keep the two in
 * step — which is the arrangement issue #996 was, one measure later.
 *
 * <p>So the list is held to the record's own components here. A field that carries a measurement and
 * is not in the map is a measure that reaches none of those readers: the shortfall of a walk that
 * ran out, or of rows that went unwatched, would be recorded on the measure and read by nobody, and
 * the behavior around it would come back whole.
 *
 * <p>Held over the components rather than over the accessors that get at the measure. Which method
 * on {@code DecisionEvidence} hands over its measurement is that type's business and is named
 * differently by each of them; that a component of this record carries one is what this is about.
 */
class EveryMeasureABehaviorIsMadeOfIsOneOfItsPartsTest {

    /**
     * The one component whose measurement is answered for somewhere other than the map.
     *
     * <p>The account is a measure of the points a behavior is owed a row at, and what each point
     * went without is the point's own answer rather than the account's — so
     * {@link BehaviorEvidence#weakening()} walks the points and unions those. Named here because an
     * exception nobody wrote down is the same silence as a missing entry.
     */
    private static final Set<String> ANSWERED_POINT_BY_POINT = Set.of("account");

    /**
     * As many parts as there are components carrying a measurement, less the one answered elsewhere.
     *
     * <p>Counted rather than matched by name. What a part is called is what a reader of a report
     * knows it by — {@code boundaryReadings} is {@code border} there — and a check that held the
     * two spellings together would be a second place the names are written. What it has to catch is
     * a field that reaches the map not at all, and a count catches that whatever either is called.
     */
    @Test
    void everyComponentThatCarriesAMeasurementIsOneOfTheParts() {
        List<String> carrying = new ArrayList<>();
        for (RecordComponent component : BehaviorEvidence.class.getRecordComponents()) {
            if (carriesAMeasurement(component.getType())
                    && !ANSWERED_POINT_BY_POINT.contains(component.getName())) {
                carrying.add(component.getName());
            }
        }

        assertEquals(carrying.size(), partsOf().size(),
                () -> "a behavior is measured by " + carrying + " and its parts are " + partsOf()
                        + ": the status, what it went without, the verdict and the document all ask"
                        + " BehaviorEvidence.parts(), and a measure that is not in it reaches none"
                        + " of them");
    }

    /** And the exception is still one, so that it is not a name left over from a field that went. */
    @Test
    void theOneAnsweredElsewhereIsStillAComponentAndStillNotAPart() {
        Set<String> components = new LinkedHashSet<>();
        for (RecordComponent component : BehaviorEvidence.class.getRecordComponents()) {
            components.add(component.getName());
        }
        for (String each : ANSWERED_POINT_BY_POINT) {
            assertTrue(components.contains(each), each + " is no longer a part of a behavior");
            assertTrue(!partsOf().contains(each),
                    each + " is in the parts, so it is answered for there and not here");
        }
    }

    /** The names the map holds, asked of an instance with nothing measured. */
    private static Set<String> partsOf() {
        return new BehaviorEvidence(Adequacy.RowReading.NOT_ASKED, null, null, null, null,
                null, null, null).parts().keySet();
    }

    /**
     * Whether values of this type carry a measurement: they are one, or they hand one over.
     *
     * <p>One level deep. A measure held inside something a component holds is that type's to answer
     * for, which is the rule the whole of this rests on.
     */
    private static boolean carriesAMeasurement(Class<?> type) {
        if (Measure.class.isAssignableFrom(type) || Measurement.class.isAssignableFrom(type)) {
            return true;
        }
        for (Method each : type.getMethods()) {
            if (each.getParameterCount() == 0
                    && (Measure.class.isAssignableFrom(each.getReturnType())
                            || Measurement.class.isAssignableFrom(each.getReturnType()))) {
                return true;
            }
        }
        return false;
    }
}
