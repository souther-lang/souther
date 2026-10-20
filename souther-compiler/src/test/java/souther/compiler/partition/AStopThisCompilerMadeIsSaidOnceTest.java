package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.BlockedDescent;
import souther.compiler.inputs.RulesLeftUnread;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.Type;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.query.Weakening;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * One position this compiler could not enter is one finding, and the findings beside it are not
 * folded away with it.
 *
 * <p>A position the walk stops at is a position whose rules nothing reached as well — the second
 * is the first said from the other end, because the rules under it would be read by a reading
 * nothing opened. Both sentences are true, and only one of them is something that went wrong.
 *
 * <p>The pairs asserted rather than a count. What is being fixed is which findings a document
 * carries, so a test that only counted them would pass over the wrong one surviving. Each of these
 * names the finding it wants and the finding it does not.
 */
class AStopThisCompilerMadeIsSaidOnceTest {

    /**
     * A list of a type that comes back to itself with no base.
     *
     * <p>The walk cannot enter an element, because there is no shape to read under it. This is the
     * stop at a position inside a container, which is where a handing over of rules would be owed
     * if the declaration had any to hand on.
     *
     * <p>The stops that remain are a type with nothing to read, and such a type states no rules to
     * hand on, so a stop and a handing over left unread are independent facts. The combinations are
     * held by the arithmetic over the arms below.
     */
    private static final String A_TYPE_NO_SHAPE_CAN_BE_READ_FROM = """
            module probe.again

            data Ok
            data Cyclic = Cyclic
            data Holder = { xs: List<Cyclic>, n: Int }
                invariant n >= 0

            behavior f : (h: Holder) -> Ok
                constructs Ok
            let f (h) = Ok
            """;

    /**
     * The stop is reported as the stop, once, and nothing is reported beside it that was not found.
     *
     * <p>No rule is handed on at a type with nothing to read, so a {@code RulesNotReached} here
     * would be a finding with nothing behind it.
     *
     * <p><b>Counted among the stops and not among the weakenings.</b> A measure of a module whose
     * bodies nothing elaborated goes without that reading as well, and says so: two facts, and an
     * author acts on each. What this is about is the stop being said once, so that is what is
     * counted — a count of everything beside it would fail the day a measure went without something
     * else, which is a different subject.
     */
    @Test
    void aPositionTheWalkCouldNotEnterIsOneFinding() {
        List<Weakening> said = weakeningOf(A_TYPE_NO_SHAPE_CAN_BE_READ_FROM, "f");

        List<Weakening> stops = said.stream()
                .filter(each -> each instanceof Weakening.ModelReadingIncomplete(
                        ClosureGap.PositionNotReachedInto _))
                .toList();
        assertEquals(1, stops.size(), () -> "one stop, one finding: " + said);
        assertTrue(stops.getFirst() instanceof Weakening.ModelReadingIncomplete(
                        ClosureGap.PositionNotReachedInto gap)
                        && gap.why() instanceof BlockReason.TypeUnresolved,
                () -> "and it is the stop itself: " + said);
        assertTrue(said.stream().noneMatch(each -> each instanceof Weakening.ModelReadingIncomplete(
                        ClosureGap.RulesNotReached _)),
                () -> "and no handing over is reported beside it: " + said);
    }

    /**
     * What each combination of the two facts comes to: a stop and a way of leaving rules unread are
     * findings of their own, and none of them hides another.
     *
     * <p>Held on a stop and on the two ways rules are left unread, each alone and a stop beside
     * each. A stop is the structure of a position the walk could not read; rules left unread are
     * what a reading lost or a recipient nothing opened. They are independent facts, so the one
     * thing said about the stop is said once whichever of the others stand beside it, and the
     * others are said whether or not it stands.
     *
     * <p>Built here rather than compiled from sources. A position that both cannot be entered and
     * hands rules on, or loses a clause of its own, is not one any model this compiler accepts
     * carries; what is being held is the arithmetic over the arms, and that is what a synthetic
     * axis is exactly good for.
     */
    @Test
    void whatEachCombinationOfFactsComesTo() {
        assertEquals(Set.of(ClosureGap.PositionNotReachedInto.class),
                gapKindsOf(residue(BLOCKED)),
                "the stop, once");
        assertEquals(Set.of(ClosureGap.PositionNotReachedInto.class,
                        ClosureGap.RulesNotReached.class),
                gapKindsOf(residue(BLOCKED, new RulesLeftUnread.ClauseOfThisReadingWasUnread())),
                "a clause this reading lost is a finding of its own beside the stop");
        assertEquals(Set.of(ClosureGap.PositionNotReachedInto.class,
                        ClosureGap.RulesNotReached.class),
                gapKindsOf(residue(BLOCKED, new RulesLeftUnread.HandoffNotAccepted())),
                "and so is a recipient nothing opened");
        assertEquals(Set.of(ClosureGap.RulesNotReached.class),
                gapKindsOf(residue(null, new RulesLeftUnread.HandoffNotAccepted())),
                "a recipient nothing opened is its own finding where the walk went on");
        assertEquals(Set.of(ClosureGap.RulesNotReached.class),
                gapKindsOf(residue(null, new RulesLeftUnread.ClauseOfThisReadingWasUnread())),
                "and so is a clause lost where nothing stopped the walk");
        assertEquals(Set.of(ClosureGap.RulesNotReached.class),
                gapKindsOf(residue(null, new RulesLeftUnread.ClauseOfThisReadingWasUnread(),
                        new RulesLeftUnread.HandoffNotAccepted())),
                "both together are one thing the measure is short of, however many ways it is");
    }

    private static final BlockedDescent BLOCKED = new BlockedDescent(new BlockReason.TypeUnresolved());

    private static ReadingResidue residue(BlockedDescent blocked, RulesLeftUnread... unread) {
        return new ReadingResidue(blocked, Set.of(unread));
    }

    /**
     * Which kinds of gap one axis carrying {@code residue} leaves the partition measure short of.
     *
     * <p>The kinds and not the values: what a gap is keyed by is the position's identity, and
     * repeating it in every row here would make every row of the arithmetic fail the day the
     * identity is revisited.
     */
    private static Set<Class<?>> gapKindsOf(ReadingResidue residue) {
        MeasureClosure.Both closed = MeasureClosure.of(
                List.of(new PositionAccount("f", TermPath.of("r").then("cost"), Type.BOOL, residue, souther.compiler.values.ValueSet.ANY,
                        null, List.of(), List.of())),
                List.of(), new LinesRead());
        return ((MeasureClosure.OfThePartition.Open) closed.partition()).by().stream()
                .map(Object::getClass).collect(java.util.stream.Collectors.toSet());
    }

    private static List<Weakening> weakeningOf(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> partitions = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        return List.copyOf(partitions.get(behavior).weakening().causes());
    }
}
