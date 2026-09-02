package souther.compiler.report;

import org.junit.jupiter.api.Test;

import souther.compiler.publish.PublicationOrders;
import souther.compiler.query.ItemAssessment.WritabilityEvidence.Ground;

import java.util.ArrayList;
import java.util.List;

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
 *
 * <p>That the order holds every ground there is, is not asked here. It is one of the things a
 * publication order can be wrong about and it is asked of every one of them at once, in
 * {@link souther.compiler.publish.EveryKindSaidInOneOrderTest}.
 */
class AGroundIsSpelledAndOrderedByTheDocumentTest {

    /** The array a document writes, in the order it writes it. The whole of the contract this file
     *  is about, written as what a reader of the document sees. */
    private static final List<String> AS_THE_DOCUMENT_WRITES_THEM =
            List.of("the_rules_prove_it", "a_row_is_at_it", "a_value_was_built");

    @Test
    void theDocumentsOrderIsTheOneWrittenDownHere() {
        List<String> written = new ArrayList<>();
        for (Object ground : PublicationOrders.WRITABILITY_GROUNDS.slots()) {
            written.add(AdequacyReport.wire((Ground) ground));
        }
        assertEquals(AS_THE_DOCUMENT_WRITES_THEM, written,
                "the order or the spelling of `writableBecause` moved, and a consumer keyed on"
                        + " either would meet a document it did not expect");
    }
}
