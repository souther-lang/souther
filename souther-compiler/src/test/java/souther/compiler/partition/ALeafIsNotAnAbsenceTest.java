package souther.compiler.partition;

import souther.compiler.ast.Ast;
import souther.compiler.check.Resolve;
import souther.compiler.check.Shape;
import souther.compiler.check.Symbols;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.types.Type;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a position is made of positions, and what that answer does not say.
 *
 * <p>The reading this protocol exists to stop is a leaf being read as a position the model does not
 * divide. Everything here is written round that: the answer for a {@code Sum} is a leaf, and a
 * {@code Sum} is exactly the position that does divide.
 */
class ALeafIsNotAnAbsenceTest {

    private static final String MODULE = """
            module demo

            data Prospecting
            data Won
            data Stage = Prospecting | Won
            data StageN = Stage
            data Cyclic = Cyclic
            data Slot = { hour: Int, room: String }
            """;

    private final Symbols symbols = Symbols.of(resolved());

    private static Ast.Module resolved() {
        Ast.Module parsed = CstFrontend.parse(MODULE);
        return Resolve.module(parsed, Symbols.of(parsed));
    }

    private StructuralInspection under(Type type) {
        return StructuralInspection.of(PartitionInput.of(type, symbols).shape(), true);
    }

    private Type named(String name) {
        return Type.ref(symbols.own(name));
    }

    // --- a leaf says one thing ------------------------------------------------------------------

    /**
     * The row that fixes the distinction. A sum answers "not made of positions", and a sum is the
     * position most likely to have had classes — so a reader that took this for "nothing divides
     * it" would be wrong about the clearest case there is.
     */
    @Test
    void aSumIsALeafAndASumIsWhatDivides() {
        assertInstanceOf(StructuralInspection.Leaf.class, under(named("Stage")));

        assertFalse(Partitions.classesOf(named("Stage"), symbols).isEmpty(),
                "the same position divides three ways, which the leaf above did not deny");
    }

    @Test
    void aScalarAndAUnitAreLeavesToo() {
        assertInstanceOf(StructuralInspection.Leaf.class, under(Type.INT));
        assertInstanceOf(StructuralInspection.Leaf.class, under(named("Prospecting")));
    }

    /** A leaf carries nothing, so there is nothing in it for a reader to turn into a conclusion. */
    @Test
    void aLeafCarriesNoReason() {
        assertEquals(new StructuralInspection.Leaf(), under(named("Stage")));
    }

    // --- what is made of positions ---------------------------------------------------------------

    @Test
    void aRecordIsItsFields() {
        StructuralInspection.Children children =
                assertInstanceOf(StructuralInspection.Children.class, under(named("Slot")));
        assertEquals(java.util.Set.of("hour", "room"), children.under().keySet());
    }

    /** A record the walk may not go into is a reaching declined, not a record with nothing in it. */
    @Test
    void aRecordTheWalkMayNotEnterIsBlockedRatherThanALeaf() {
        StructuralInspection stopped = StructuralInspection.of(
                PartitionInput.of(named("Slot"), symbols).shape(), false);
        assertEquals(new StructuralInspection.Blocked(new BlockReason.DepthLimit()), stopped);
    }

    // --- and what stops the derivation -------------------------------------------------------------

    /**
     * Issue #626, as this protocol states it: the shape is understood and the reaching is not made.
     *
     * <p>A fallback and not a verdict. The same position takes a line from
     * {@code guard List.length(items) < 3}, and where one is drawn this reason is never reported —
     * what a block refuses is a rule about what is inside standing in for reaching inside.
     */
    @Test
    void aSequenceIsBlockedOnReachingItsElements() {
        assertEquals(new StructuralInspection.Blocked(new BlockReason.UnsupportedTraversal(
                        BlockReason.Traversal.SEQUENCE_ELEMENT)),
                under(Type.list(named("Slot"))));
        assertEquals(new StructuralInspection.Blocked(new BlockReason.UnsupportedTraversal(
                        BlockReason.Traversal.SEQUENCE_ELEMENT)),
                under(Type.set(named("Slot"))));
    }

    /** Each of the three is its own reaching, so implementing one does not read as all three. */
    @Test
    void theOtherTwoReachingsAreToldApartFromIt() {
        assertEquals(new StructuralInspection.Blocked(new BlockReason.UnsupportedTraversal(
                        BlockReason.Traversal.OPTIONAL_VALUE)),
                under(Type.option(Type.INT)));
        assertEquals(new StructuralInspection.Blocked(new BlockReason.UnsupportedTraversal(
                        BlockReason.Traversal.MAPPING_CONTENT)),
                under(Type.map(Type.STRING, Type.INT)));
    }

    /** A declaration reachable from itself: interpreted as far as it goes, which is not far enough. */
    @Test
    void aTypeThisCouldNotInterpretIsBlockedRatherThanALeaf() {
        assertEquals(new StructuralInspection.Blocked(new BlockReason.TypeUnresolved()),
                under(named("Cyclic")));
    }

    /** A name round a position changes neither what is under it nor whether anything is. */
    @Test
    void aNameRoundAPositionChangesNothingHere() {
        assertEquals(under(named("Stage")), under(named("StageN")));
    }

    // --- the answers a leaf and a block are not -----------------------------------------------------

    /**
     * Nothing here answers whether the position divides. A conclusion of that kind needs the phases
     * after this one, and the type offers no way to reach one from here — held as a test so that
     * adding such a way is a change somebody has to make on purpose.
     */
    @Test
    void nothingHereAnswersWhetherThePositionDivides() {
        for (java.lang.reflect.Method method : StructuralInspection.class.getMethods()) {
            assertFalse(UndividedPosition.class.isAssignableFrom(method.getReturnType()),
                    "`" + method.getName() + "` turns a structural answer into a report of a"
                            + " position the model does not divide, which it cannot know");
        }
        assertTrue(StructuralInspection.class.isSealed());
    }
}
