package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.OfferingRequest;
import souther.compiler.report.GeneratedRows;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A set states no order, and the row offered for a caller of a behavior is the callee's row written
 * again. Written in the order of the elements' text, {@code N(10)} comes before {@code N(2)} and the
 * row no longer reads as the one its author wrote.
 */
class ARowLiftedFromACalleeWritesASetInTheOrderOfItsValuesTest {

    private static final String MODEL = """
            module repro.fallen

            data N = Int
                invariant value >= 1 && value <= 12

            data Fallen = Set<N>

            behavior count : (f: Fallen) -> Int

            let count (f) = Set.size(f.value)

            example count
                | (Fallen([N(2), N(9), N(10)])) -> 3

            behavior twice : (f: Fallen) -> Int

            let twice (f) = count(f) * 2

            example twice
                | (Fallen([N(1)])) -> 2
            """;

    @Test
    void theRowOfTheCalleeIsOfferedWithItsElementsInTheOrderOfTheirValues() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(e -> e.diagnostic().code().toString()).toList());

        String offered = GeneratedRows.of(Adequacy.offeredFor(compilation.db(),
                        OfferingRequest.overTheModule("repro.fallen")),
                Map.of(), SourceRendering.namedByIdentity(compilation.texts()),
                compilation.db()).text();

        assertTrue(offered.contains("(Fallen([N(2), N(9), N(10)]))"), offered);
        assertFalse(offered.contains("N(10), N(2)"), offered);
    }
}
