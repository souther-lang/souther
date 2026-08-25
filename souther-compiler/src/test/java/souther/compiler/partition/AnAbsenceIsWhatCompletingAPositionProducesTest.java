package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.EveryShippedMessageCatalogIsCompleteAndValidTest;
import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.StructuralInspection;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.Type;

import java.io.IOException;
import java.nio.charset.StandardCharsets;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * "The model divides this position no way" is the end of a chain, not a value anything can write.
 *
 * <p>It was a value anything could write, and everything that could not answer wrote it: a walk
 * that fell out of the bottom of a chain of conditions, a reader that stopped at a name, a rule
 * nothing could turn into a line. What all of those have in common is that they say something about
 * this compiler, and the sentence they produced says something about the model.
 *
 * <p>So the chain is the type. A position is read; where the producers of local evidence came back
 * with nothing it becomes a {@link PendingPosition}; and completing one of those with what the
 * rules came to is what produces the absence. It is the one arm where nothing stopped and nothing
 * was found.
 *
 * <p>What is held here is that arm and its neighbours. That nothing outside this package can start
 * the chain halfway through is the visibility of {@link PendingPosition}, which no test in this
 * package can show — the scan below is a tripwire over where the one absence is named, not a proof
 * that it cannot be reached another way.
 */
class AnAbsenceIsWhatCompletingAPositionProducesTest {

    private static final TermPath AT = TermPath.of("x");

    private static final AxisId ID = AxisId.of("run", new NumericTerm.ValueOf(AT));

    private static Axis measured() {
        return new Axis(ID, new NumericTerm.ValueOf(AT), Type.BOOL,
                List.of(PartitionClass.of("true", "true", new Recognition.Nothing(),
                        RepresentativeSource.of(FixtureTemplate.bool(true)))),
                List.of());
    }

    private static Axis pending(StructuralInspection.Continuation found) {
        return pending(found, null);
    }

    /** The same, with a rule about the position's own values that the local reading could not take
     *  in — which is a second way a position can be left unable to reach an absence. */
    private static Axis pending(StructuralInspection.Continuation found, BlockReason unread) {
        return Axis.pendingAt(ID, new NumericTerm.ValueOf(AT), Type.BOOL, false, found, unread);
    }

    /**
     * A leaf carrying a rule the local reading could not take in cannot reach an absence either.
     *
     * <p>The other way a position is left unable to say the model divides it no way. Nothing under
     * it stopped the walk — it is a leaf — and a rule about its own values was written and not
     * read, so what a body says next decides whether it is measured, and never that the model
     * states nothing here.
     */
    @Test
    void aLeafCarryingAnUnreadRuleCompletesAsThatRule() {
        BlockReason unread = new BlockReason.UnreadValueRule();

        UndividedPosition said = PendingPosition.of(pending(new StructuralInspection.Continuation.None(), unread))
                .complete(new BodyCutInspection.Exhausted());

        assertFalse(said.isAbsent(), said.toString());
        // And the verdict says only that: what stopped it is the rule's, said by the reader that
        // read the rule and naming which rule it was.
        assertNull(PendingPosition.of(pending(new StructuralInspection.Continuation.None(), unread))
                        .reportable(),
                "a rule this read and could not use is not a position nothing was reached at");
    }

    /**
     * Neither of two rules becomes the position's account, where a body's comparison came to
     * nothing as well.
     *
     * <p>Both are rules this read and could not use, and each is said by the reader that read it,
     * naming which rule. There used to be one line here and a precedence deciding which of the two
     * reasons it carried — which is the shape of it: an author was told one limit and never
     * learnt that the other rule existed. What the position itself has to say is that nothing was
     * established, and no more.
     */
    @Test
    void twoRulesLeaveThePositionWithNoAccountOfItsOwn() {
        PendingPosition pending = PendingPosition.of(pending(new StructuralInspection.Continuation.None(),
                new BlockReason.UnreadValueRule()));

        assertFalse(pending.complete(new BodyCutInspection.Blocked()).isAbsent());
        assertNull(pending.reportable(), "each rule is said with its rule, not as this position");
    }

    // --- what can be pending at all -------------------------------------------------------------

    /** A position with evidence is not pending anything, so there is nothing to complete and no way
     *  to an absence from it. */
    @Test
    void aPositionWithEvidenceIsNotPending() {
        assertNull(PendingPosition.of(measured()));
    }

    /** And a position with no evidence that nothing read is not answered for at all: what would be
     *  said of it is this compiler's state, written down as what the model divides. */
    @Test
    void aPositionNothingReadIsNotAnsweredFor() {
        assertThrows(IllegalStateException.class, () -> PendingPosition.of(
                new Axis(ID, new NumericTerm.ValueOf(AT), Type.BOOL, List.of(), List.of())));
    }

    @Test
    void aPositionWithoutEvidenceIsPendingWhatItsStructureFound() {
        assertEquals(new PendingPosition.Leaf(AT),
                PendingPosition.of(pending(new StructuralInspection.Continuation.None())));
        assertEquals(new PendingPosition.Blocked(AT, new BlockReason.TypeUnresolved()),
                PendingPosition.of(pending(
                        new StructuralInspection.Continuation.Blocked(new BlockReason.TypeUnresolved()))));
    }

    // --- and what completing one comes to -------------------------------------------------------

    /** The one arm that reaches an absence: nothing under the position, and every rule about it
     *  read and drawing nothing. */
    @Test
    void aLeafWhoseRulesWereAllReadAndDrewNothingIsAnAbsence() {
        UndividedPosition done = new PendingPosition.Leaf(AT)
                .complete(new BodyCutInspection.Exhausted());

        assertTrue(done.isAbsent());
        assertEquals(AT, done.at());
    }

    /** A rule about the position that went unread is what it is left with, and not an absence. */
    @Test
    void aLeafWhoseRuleWentUnreadSaysThat() {
        UndividedPosition done = new PendingPosition.Leaf(AT)
                .complete(new BodyCutInspection.Blocked());

        assertFalse(done.isAbsent());
        assertEquals(new UndividedPosition.Why.CannotDerive(), done.why());
    }

    /**
     * A reading that stopped stays what the position is left with, whatever the rules came to.
     *
     * <p>Both rows, because the precedence is only visible where the other side has something to
     * say: where the walk could not reach into what a position holds, a rule naming something
     * inside it describes the same stop from the other end, and the first is the cause (issue
     * #626).
     */
    @Test
    void aReadingThatStoppedOutranksWhatTheRulesCameTo() {
        PendingPosition blocked = new PendingPosition.Blocked(AT,
                new BlockReason.UnsupportedTraversal(BlockReason.Traversal.OPTIONAL_VALUE));
        UndividedPosition.Why expected = new UndividedPosition.Why.CannotDerive();

        assertEquals(expected, blocked.complete(new BodyCutInspection.Exhausted()).why());
        assertEquals(expected, blocked.complete(new BodyCutInspection.Blocked()).why());
        // And the finding is the stop, whatever the rules came to: a rule naming something inside a
        // position the walk could not enter describes that same stop from the other end.
        assertEquals(new souther.compiler.inputs.PositionReadingBlocked(AT,
                        new BlockReason.UnsupportedTraversal(
                                BlockReason.Traversal.OPTIONAL_VALUE)),
                blocked.reportable());
    }

    /** A line drawn at a position whose axis says it has none is two readings disagreeing, and
     *  neither of them is a thing to report about a model. */
    @Test
    void aLineDrawnAtAPositionWithNoEvidenceIsNotAnswered() {
        assertThrows(IllegalStateException.class, () -> new PendingPosition.Leaf(AT)
                .complete(new BodyCutInspection.Evidence()));
        assertThrows(IllegalStateException.class, () -> new PendingPosition
                .Blocked(AT, new BlockReason.DepthLimit())
                .complete(new BodyCutInspection.Evidence()));
    }

    // --- and nothing else makes one -------------------------------------------------------------

    /**
     * Held over the sources, because what it says cannot be said in a test: outside this package
     * the absence has no constructor to call and no instance to name, and inside it the one
     * instance is reached through the completion.
     *
     * <p>A tripwire. Naming the field from a third place in this package defeats it, and that is
     * the line this fails on.
     */
    @Test
    void theAbsenceIsNamedOnlyWhereItIsProduced() throws IOException {
        List<Path> sources = EveryShippedMessageCatalogIsCompleteAndValidTest.mainSources();
        assertFalse(sources.isEmpty(), "found no sources at all — the scan missed the tree");

        Set<String> naming = new TreeSet<>();
        Set<String> producing = new TreeSet<>();
        for (Path source : sources) {
            String text = Files.readString(source, StandardCharsets.UTF_8);
            if (text.contains("Absent.PROVEN")) {
                naming.add(source.getFileName().toString());
            }
            if (text.contains("absentAfter(")) {
                producing.add(source.getFileName().toString());
            }
        }

        assertEquals(Set.of("UndividedPosition.java"), naming,
                "the one absence is named where it is declared");
        assertEquals(Set.of("UndividedPosition.java", "PendingPosition.java"), producing,
                "and is produced by completing a position, which is what makes it a conclusion");
    }
}
