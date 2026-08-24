package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.query.ItemAssessment.WritabilityEvidence.Ground;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * How a document spells the grounds and what order it puts them in are the document's, not the type's.
 *
 * <p>Two decisions that look like one. Which words a consumer must handle is the contract, and
 * renaming a constant inside the compiler is not — that half was already written out. The other half
 * is the order, and it was read off {@code Ground.values()}: an editor moving two constants apart
 * would have moved the bytes of every document ever written, and the test that was meant to hold the
 * order compared against {@code values()} as well, so it would have moved with them and said nothing.
 *
 * <p>So both are held here against fixed strings. Nothing in this file mentions a constant except to
 * say which word it is spelled as, and a change to the type that a consumer would notice cannot pass
 * without changing a literal somebody has to read.
 */
class AGroundIsSpelledAndOrderedByTheDocumentTest {

    /** The array a document writes, in the order it writes it. The whole of the contract this file
     *  is about, written as what a reader of the document sees. */
    private static final List<String> AS_THE_DOCUMENT_WRITES_THEM =
            List.of("the_rules_prove_it", "a_row_is_at_it", "a_value_was_built");

    @Test
    void theDocumentsOrderIsTheOneWrittenDownHere() {
        List<String> written = new ArrayList<>();
        AdequacyReport.GROUND_ORDER.forEach(ground -> written.add(AdequacyReport.wire(ground)));
        assertEquals(AS_THE_DOCUMENT_WRITES_THEM, written,
                "the order or the spelling of `writableBecause` moved, and a consumer keyed on"
                        + " either would meet a document it did not expect");
    }

    /**
     * Every ground there is reaches a document.
     *
     * <p>The order is a list and a list can be short. A ground added to the type and left out of it
     * is one no document carries — the widening would be made, every other test would go on passing,
     * and the field would quietly answer a narrower question than the type does.
     */
    @Test
    void theDocumentWritesEveryGroundThereIs() {
        assertEquals(Set.of(Ground.values()), Set.copyOf(AdequacyReport.GROUND_ORDER),
                "a ground the type has that the document never writes");
        assertEquals(AdequacyReport.GROUND_ORDER.size(),
                Set.copyOf(AdequacyReport.GROUND_ORDER).size(), "and none of them twice");
    }
}
