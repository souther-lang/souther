package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.semantics.OperationLaw;
import souther.compiler.types.ValueName;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * The facts read off the proofs shipped with this compiler are the facts proving the library here
 * comes to: every observation settled the same way, by the same law or the same closing, and the
 * same statements left unproved.
 *
 * <p>Asked of the record the build wrote, which is what a compilation reads. That the record is
 * there is part of the claim: a build that wrote none would have every compilation prove the
 * library at its start, with nothing failing.
 */
class TheProofsShippedAreWhatProvingTheLibraryComesToTest {

    @Test
    void theBuildShipsWhatProvingTheLibraryCameTo() {
        assertNotNull(LibraryProofsAsBuilt.class.getClassLoader()
                        .getResource(LibraryProofsAsBuilt.RESOURCE),
                "the build writes the proofs it shipped beside the classes");
    }

    @Test
    void whatIsReadOffThemIsWhatProvingComesTo() {
        BoundOperationFacts proved = OperationFactBinder.bindAll(DefaultStdlib.get());
        BoundOperationFacts shipped = DefaultBoundOperationFacts.get();
        assertEquals(settlings(proved), settlings(shipped),
                "each observation settled as proving settles it");
        assertEquals(proved.notProvedOfTheirBodies(), shipped.notProvedOfTheirBodies(),
                "the same statements left unproved");
    }

    /** How each observation is settled, told apart by what settles it and not by how it came to
     *  be known: a law proved here and the same law proved when this was built are one law. */
    private static Map<ValueName, Map<OperationLaw.Observed, Object>> settlings(
            BoundOperationFacts facts) {
        Map<ValueName, Map<OperationLaw.Observed, Object>> out = new LinkedHashMap<>();
        facts.settled().forEach((operation, of) -> {
            Map<OperationLaw.Observed, Object> each = new LinkedHashMap<>();
            of.forEach((observed, settled) -> each.put(observed, switch (settled) {
                case BoundOperationFacts.Settled.ByALaw(var law, var _) -> law;
                case BoundOperationFacts.Settled.Unsaid unsaid -> unsaid;
                case BoundOperationFacts.Settled.Open open -> open;
            }));
            out.put(operation, each);
        });
        return out;
    }
}
