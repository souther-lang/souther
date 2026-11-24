package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Text;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * What {@link FixtureTemplate#on} writes at a place of a carrier reads back as the value the
 * carrier stands for at that place, so a value built as a template and one read off a run are one.
 */
class ATemplateReadsBackAsTheValueItWasWrittenForTest {

    @Test
    void aScalarReadsBackAsTheValueItsCarrierStandsForAtThePlace() {
        List<Carrier> carriers = List.of(Carrier.WHOLE, Carrier.DENSE, Carrier.DATE,
                Carrier.MOMENT, Carrier.TIME, Carrier.INSTANT, Carrier.TEXT);
        for (Carrier carrier : carriers) {
            for (Place at : placesOf(carrier)) {
                FixtureTemplate written = FixtureTemplate.on(carrier, at, name -> null);
                assertEquals(carrier.valueOf(at), written.observed(), carrier + " at " + at);
            }
        }
    }

    @Test
    void whatIsNotABareScalarReadsBackAsNothing() {
        assertNull(FixtureTemplate.none().observed());
        assertNull(FixtureTemplate.collection(List.of(FixtureTemplate.integer(1))).observed());
    }

    private static List<Place> placesOf(Carrier carrier) {
        if (carrier == Carrier.TEXT) {
            return List.of(Text.of("a\"b"));
        }
        List<Place> out = new ArrayList<>(List.of(Count.of(0), Count.of(7)));
        if (carrier == Carrier.WHOLE) {
            out.add(Count.of(-3));
        }
        if (carrier == Carrier.DENSE) {
            out.add(new Count(new BigDecimal("-1.25")));
        }
        return out;
    }
}
