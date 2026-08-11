package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * Two vocabularies, on purpose. What this compiler could not do is recorded as precisely as it is
 * worth recording; what a document promises its reader they can tell apart is coarser, and moves
 * when a reader would act on the difference rather than when a capability changes here.
 *
 * <p>Held as one type, the coarse one governed the precise one: a reason could not be made sharper
 * without widening a published vocabulary, so the pressure was always back to a word that already
 * existed. The projection is what keeps them apart while keeping them honest.
 */
class WhyADerivationStoppedIsNotWhatAReportPromisesTest {

    /**
     * The collapse, written down where it can be reviewed. Three missing traversals are one word a
     * report writes, because a reader of the report cannot act on which of them it was — the model
     * is the same either way.
     */
    @Test
    void everyMissingTraversalIsOneWordInAReport() {
        for (BlockReason.Traversal traversal : BlockReason.Traversal.values()) {
            assertEquals(UndividedPosition.Reason.UNSUPPORTED_TRAVERSAL,
                    ReportedReason.of(new BlockReason.UnsupportedTraversal(traversal)),
                    traversal + " is reported as a traversal this does not make");
        }
    }

    /** And the ones a reader can act on differently keep their own word. */
    @Test
    void theOthersAreTheirOwnWord() {
        assertEquals(UndividedPosition.Reason.TYPE_UNRESOLVED,
                ReportedReason.of(new BlockReason.TypeUnresolved()));
        assertEquals(UndividedPosition.Reason.DEPTH_LIMIT,
                ReportedReason.of(new BlockReason.DepthLimit()));
    }

    /**
     * Which traversals are told apart here is a claim about what would lift each: choosing among a
     * sequence's elements, choosing whether an optional holds one, and deciding what part of a
     * mapping a rule is about are three pieces of work. Written out so that collapsing two of them
     * is a change to this test rather than a quiet edit.
     */
    @Test
    void theTraversalsToldApartAreTheOnesLiftedByDifferentWork() {
        assertEquals(Set.of(BlockReason.Traversal.SEQUENCE_ELEMENT,
                        BlockReason.Traversal.OPTIONAL_VALUE,
                        BlockReason.Traversal.MAPPING_CONTENT),
                Set.of(BlockReason.Traversal.values()));
    }

    /** Every reason has a word. The compiler holds this — the projection carries no {@code default}
     *  — and this says so where a reader looks for it. */
    @Test
    void everyReasonHasAWord() {
        for (BlockReason reason : new BlockReason[] {
                new BlockReason.TypeUnresolved(),
                new BlockReason.DepthLimit(),
                new BlockReason.UnsupportedTraversal(BlockReason.Traversal.SEQUENCE_ELEMENT)}) {
            assertNotNull(ReportedReason.of(reason), reason + " is reported as something");
        }
    }
}
