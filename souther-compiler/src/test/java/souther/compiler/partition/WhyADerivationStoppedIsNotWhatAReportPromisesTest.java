package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.Set;

import souther.compiler.inputs.BlockReason;
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
     * The collapse, written down where it can be reviewed. Every missing traversal is one word a
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
        assertEquals(UndividedPosition.Reason.RETURNS_TO_A_DECLARATION_ALREADY_READ,
                ReportedReason.of(aReturn()));
    }

    /** A path that came back to a declaration it had opened, as a reason on its own. */
    private static BlockReason.RecursiveExpansion aReturn() {
        return new BlockReason.RecursiveExpansion(
                souther.compiler.types.TypeSymbols.declared(
                        new souther.compiler.types.TypeKey("g", "Chain")),
                souther.compiler.inputs.TermPath.of("c"));
    }

    /**
     * Which traversals are named here is a claim about what is still not reached, and it shrinks as
     * the reachings are made: a sequence's elements are positions of the input, and so is what an
     * optional holds — a branch under the narrowing that it holds one. What is left is deciding
     * what part of a mapping a rule is about, which nothing has decided. Written out so that a
     * reaching leaving this list is a change to this test rather than a quiet edit.
     */
    @Test
    void theTraversalsNamedAreTheOnesStillNotMade() {
        assertEquals(Set.of(BlockReason.Traversal.MAPPING_CONTENT),
                Set.of(BlockReason.Traversal.values()));
    }

    /** Every reason has a word. The compiler holds this — the projection carries no {@code default}
     *  — and this says so where a reader looks for it. */
    @Test
    void everyReasonHasAWord() {
        for (BlockReason reason : new BlockReason[] {
                new BlockReason.TypeUnresolved(),
                aReturn(),
                new BlockReason.UnsupportedTraversal(BlockReason.Traversal.MAPPING_CONTENT)}) {
            assertNotNull(ReportedReason.of(reason), reason + " is reported as something");
        }
    }
}
