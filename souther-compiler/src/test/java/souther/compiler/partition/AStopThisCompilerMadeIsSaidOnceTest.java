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
import static org.junit.jupiter.api.Assertions.assertThrows;
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
     * A sum one of whose cases holds the sum again.
     *
     * <p>The walk stops at the tail, because that is a return to the declaration it has already
     * opened. A sum states nothing about every value of it and hands its rules on to its cases, so
     * the tail is a position rules were handed on at — and the stop is why nothing took them.
     */
    private static final String A_RETURN_TO_A_SUM = """
            module probe.again

            data Ok
            data Amount = Int
                invariant ranged = value >= 0 && value <= 100
            data Nil
            data Cons = { head: Amount, tail: Chain }
            data Chain = Nil | Cons

            behavior f : (c: Chain) -> Ok
                constructs Ok
            let f (c) = Ok
            """;

    /**
     * The stop is reported as the stop, and the handing over it left standing is not reported again.
     *
     * <p>{@code RulesNotReached} here would be the consequence of the finding beside it and not a
     * second thing an author could act on.
     *
     * <p><b>Counted among the stops and not among the weakenings.</b> A measure of a module whose
     * bodies nothing elaborated goes without that reading as well, and says so: two facts, and an
     * author acts on each. What this is about is the stop being said once, so that is what is
     * counted — a count of everything beside it would fail the day a measure went without something
     * else, which is a different subject.
     */
    @Test
    void aPositionTheWalkCouldNotEnterIsOneFinding() {
        List<Weakening> said = weakeningOf(A_RETURN_TO_A_SUM, "f");

        List<Weakening> stops = said.stream()
                .filter(each -> each instanceof Weakening.ModelReadingIncomplete(
                        ClosureGap.PositionNotReachedInto _))
                .toList();
        assertEquals(1, stops.size(), () -> "one stop, one finding: " + said);
        assertTrue(stops.getFirst() instanceof Weakening.ModelReadingIncomplete(
                        ClosureGap.PositionNotReachedInto gap)
                        && gap.why() instanceof BlockReason.RecursiveExpansion,
                () -> "and it is the stop itself: " + said);
        assertTrue(said.stream().noneMatch(each -> each instanceof Weakening.ModelReadingIncomplete(
                        ClosureGap.RulesNotReached _)),
                () -> "and the handing over it left standing is that same stop: " + said);
    }

    /**
     * A handing over left standing by a blocked descent may not travel without the descent.
     *
     * <p>The transport half. Which of the two the reading found is settled where both were in hand,
     * and every rebuild of an axis after that is a place one of them can be dropped — a position
     * whose elements could not be reached came back out of the second phase with nothing to say it
     * had ever stopped, once. Dropped here, the arm would fold into a finding nothing writes and the
     * stop would go unsaid, so the pair is refused rather than reported short.
     */
    @Test
    void anArmNamingABlockedDescentMayNotTravelWithoutIt() {
        assertThrows(IllegalArgumentException.class,
                () -> new ReadingResidue(null,
                        Set.of(new RulesLeftUnread.Handoff(
                                new RulesLeftUnread.HandoffUnread.FromBlockedDescent()))),
                "the arm names a descent this residue does not carry");
    }

    /**
     * Every way the two facts can arrive together, and what each comes to.
     *
     * <p><b>The relation and not one direction of it.</b> Which findings a residue comes to is a
     * biconditional between what the ledger recorded and what the walk found, crossed with the one
     * fold. Asserted a case at a time from whichever side a reader happens to be building, each
     * assertion holds the half it was written for — which is how one stop came to be written from
     * two ends with nothing relating them in the first place (issue #1084).
     *
     * <p>Built here rather than compiled from sources. Two of the six rows are this compiler
     * contradicting itself and no model produces them, and a row of the other four needs a position
     * that both loses a clause of its own and cannot be entered, which no model this compiler
     * accepts carries either. What is being held is the arithmetic over the arms, and that is what a
     * synthetic axis is exactly good for.
     */
    @Test
    void whatEachPairOfFactsComesTo() {
        // The walk could not go in, and the handing over it left standing is that same stop.
        assertEquals(Set.of(ClosureGap.PositionNotReachedInto.class),
                gapKindsOf(residue(BLOCKED, fromBlockedDescent())),
                "the stop, once");
        // And a clause this reading lost beside it is a finding of its own, at the same path.
        // The one the issue names: folded on the path, this one goes with the other.
        assertEquals(Set.of(ClosureGap.PositionNotReachedInto.class,
                        ClosureGap.RulesNotReached.class),
                gapKindsOf(residue(BLOCKED,
                        new RulesLeftUnread.ClauseOfThisReadingWasUnread(),
                        fromBlockedDescent())),
                "a clause this reading lost is not the stop, and does not fold into it");
        // The walk went on and left a recipient with no reading. Nothing else says so.
        assertEquals(Set.of(ClosureGap.RulesNotReached.class),
                gapKindsOf(residue(null, notFullyAccepted())),
                "a recipient nothing opened is its own finding");
        assertEquals(Set.of(ClosureGap.RulesNotReached.class),
                gapKindsOf(residue(null, new RulesLeftUnread.ClauseOfThisReadingWasUnread())),
                "and so is a clause lost where nothing stopped the walk");

        // And the two rows where the ledger and the walk contradict each other. Neither is a state
        // of a model: over an owed handing over, nobody was named as a recipient exactly where the
        // walk could not go in. Let through, the second is #1084's two entries reached another way.
        assertThrows(IllegalArgumentException.class,
                () -> residue(BLOCKED, notFullyAccepted()),
                "a recipient was named at a position the walk could not enter");
        assertThrows(IllegalArgumentException.class,
                () -> residue(null, fromBlockedDescent()),
                "nobody was named at a position the walk went into");
    }

    private static final BlockedDescent BLOCKED = new BlockedDescent(new BlockReason.TypeUnresolved());

    private static RulesLeftUnread fromBlockedDescent() {
        return new RulesLeftUnread.Handoff(
                new RulesLeftUnread.HandoffUnread.FromBlockedDescent());
    }

    private static RulesLeftUnread notFullyAccepted() {
        return new RulesLeftUnread.Handoff(
                new RulesLeftUnread.HandoffUnread.NotFullyAccepted());
    }

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
