package souther.compiler.inputs;

import souther.compiler.DefaultStdlib;
import souther.compiler.ast.Ast;
import souther.compiler.ast.Hir;
import souther.compiler.check.Resolve;
import souther.compiler.check.SyntaxSymbols;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeView;
import souther.compiler.frontend.CstFrontend;
import souther.compiler.partition.UndividedPosition;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a position stands once what follows it has been read, and what that answer does not say.
 *
 * <p>The reading this protocol exists to stop is a position that stands with nothing following it
 * being read as a position the model does not divide. Everything here is written round that: a sum
 * stands and continues into its cases, and a sum is exactly the position that does divide.
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
            data Approved = { id: Int }
            data Rejected = { why: String }
            data Decision = Approved | Rejected
            """;

    private final Symbols symbols = Symbols.of(resolved(), DefaultStdlib.get());

    private static Hir.Module resolved() {
        Ast.Module parsed = CstFrontend.parse(MODULE);
        return Resolve.module(parsed, SyntaxSymbols.of(parsed, DefaultStdlib.get()));
    }

    private StructuralInspection under(Type type) {
        return under(type, true);
    }

    private StructuralInspection under(Type type, boolean deeper) {
        TypeView view = TypeView.of(type, symbols);
        return StructuralInspection.of(ReadablePosition.of(view).shape(), deeper,
                Distinctions.ofType(view, symbols));
    }

    private static StructuralInspection retained(StructuralInspection.Continuation continuation) {
        return new StructuralInspection.Retained(continuation);
    }

    private StructuralInspection.Branch unitCase(String name) {
        return new StructuralInspection.Branch(
                Refinement.sumCase(((Type.Ref) named(name)).name()), null);
    }

    private Type named(String name) {
        return Type.ref(TypeSymbols.declared(new TypeKey(symbols.module(), name)));
    }

    // --- a leaf says one thing ------------------------------------------------------------------

    /**
     * The row that fixes the distinction. A sum answers "not made of positions", and a sum is the
     * position most likely to have had classes — so a reader that took this for "nothing divides
     * it" would be wrong about the clearest case there is.
     */
    @Test
    void aSumStandsAndASumIsWhatDivides() {
        assertEquals(retained(new StructuralInspection.Continuation.Branches(
                        List.of(unitCase("Prospecting"), unitCase("Won")))),
                under(named("Stage")));

        assertFalse(Distinctions.ofType(TypeView.of(named("Stage"), symbols), symbols).isEmpty(),
                "the same position divides two ways, which the answer above did not deny");
    }

    /**
     * A branch of a sum exists whether or not anything stands under it.
     *
     * <p>Both of {@code Stage}'s cases are the whole of a value, so nothing stands under either —
     * and both are branches all the same. Read as "no continuation, so no branch", the case would
     * go from what a row is owed at the position.
     */
    @Test
    void aUnitCaseIsABranchWithNothingUnderIt() {
        StructuralInspection.Continuation.Branches branches =
                assertInstanceOf(StructuralInspection.Continuation.Branches.class,
                        assertInstanceOf(StructuralInspection.Retained.class,
                                under(named("Stage"))).continuation());
        assertEquals(2, branches.branches().size());
        branches.branches().forEach(each -> assertEquals(null, each.under(),
                () -> each.refinement() + " is the whole of a value and holds no position"));
    }

    /** And a case that carries a record continues into it, at the same position. */
    @Test
    void aCaseThatCarriesAValueContinuesIntoIt() {
        StructuralInspection.Continuation.Branches branches =
                assertInstanceOf(StructuralInspection.Continuation.Branches.class,
                        assertInstanceOf(StructuralInspection.Retained.class,
                                under(named("Decision"))).continuation());
        assertEquals(List.of(named("Approved"), named("Rejected")),
                branches.branches().stream().map(StructuralInspection.Branch::under).toList());
    }

    @Test
    void aScalarAndAUnitStandWithNothingAfterThem() {
        assertEquals(retained(new StructuralInspection.Continuation.None()), under(Type.INT));
        assertEquals(retained(new StructuralInspection.Continuation.None()),
                under(named("Prospecting")));
    }

    // --- what is made of positions ---------------------------------------------------------------

    @Test
    void aRecordIsItsFields() {
        StructuralInspection.Decomposed decomposed =
                assertInstanceOf(StructuralInspection.Decomposed.class, under(named("Slot")));
        assertEquals(java.util.Set.of("hour", "room"), decomposed.under().keySet());
    }

    /** A record the walk may not go into is a reaching declined, not a record with nothing in it. */
    @Test
    void aRecordTheWalkMayNotEnterIsBlockedRatherThanEmpty() {
        assertEquals(blocked(new BlockReason.DepthLimit()), under(named("Slot"), false));
    }

    private static StructuralInspection blocked(BlockReason.AboutThePosition why) {
        return retained(new StructuralInspection.Continuation.Blocked(why));
    }

    // --- and what stops the derivation -------------------------------------------------------------

    /**
     * A sequence holds a position, and is one.
     *
     * <p>Neither of the two answers the other shapes get. A record is given up in favour of its
     * fields, because it states nothing of its own; a sequence carries a length that
     * {@code guard List.length(items) < 3} draws a line on, so it stays a position to be answered
     * for and what it holds is read beside it.
     */
    @Test
    void aSequenceHoldsAPositionAndIsStillOne() {
        for (Type carrier : List.of(Type.list(named("Slot")), Type.set(named("Slot")))) {
            assertEquals(retained(new StructuralInspection.Continuation.Elements(named("Slot"))),
                    under(carrier));
            assertInstanceOf(StructuralInspection.Retained.class, under(carrier),
                    () -> "and is still to be answered for: " + carrier);
        }
    }

    /** And the walk stopping is the walk's own answer, said as the depth it is. */
    @Test
    void aSequenceTheWalkMayNotEnterIsStoppedByTheDepthAndNotByItsShape() {
        assertEquals(blocked(new BlockReason.DepthLimit()), under(Type.list(named("Slot")), false));
    }

    /** Each of the three is its own reaching, so implementing one does not read as all three. */
    @Test
    void theOtherTwoReachingsAreToldApartFromIt() {
        assertEquals(blocked(new BlockReason.UnsupportedTraversal(
                        BlockReason.Traversal.OPTIONAL_VALUE)),
                under(Type.option(Type.INT)));
        assertEquals(blocked(new BlockReason.UnsupportedTraversal(
                        BlockReason.Traversal.MAPPING_CONTENT)),
                under(Type.map(Type.STRING, Type.INT)));
    }

    /** A declaration reachable from itself: interpreted as far as it goes, which is not far enough. */
    @Test
    void aTypeThisCouldNotInterpretIsBlockedRatherThanEmpty() {
        assertEquals(blocked(new BlockReason.TypeUnresolved()), under(named("Cyclic")));
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
