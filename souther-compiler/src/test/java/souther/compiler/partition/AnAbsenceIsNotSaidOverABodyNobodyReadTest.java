package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.BlockedDescent;
import souther.compiler.inputs.StructuralInspection;
import souther.compiler.inputs.TermPath;
import souther.compiler.types.Type;
import souther.compiler.values.ValueSet;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * "The model divides this position no way" is not said where nothing read the body.
 *
 * <p>{@link UndividedPosition.Why.Absent} is a conclusion about a model: every rule about the
 * position was read and none of them divides it. The phases that read the declarations answer for
 * what they saw, and where the body was never elaborated the rules it writes were not among them —
 * so the same position reached the same completion and the conclusion drawn from it was one nobody
 * was entitled to draw.
 *
 * <p>Held as a law over the value rather than at the one model that showed it. What decides this is
 * what the partition measure's reading came to, and every position of every behavior whose body
 * this image has none of arrives here the same way.
 *
 * <p>The three closures are all here, because withholding it everywhere would be a different
 * defect: a reading that ran out and one that stopped on a gap it can name both read the body, and
 * what they came to at a position they answered for is theirs to say.
 */
class AnAbsenceIsNotSaidOverABodyNobodyReadTest {

    private static final TermPath AT = TermPath.of("n");

    /**
     * A position the readings answered for, with nothing under it and no rule filed at it.
     *
     * <p>Which is the one state an absence follows from. Everything below is this position under a
     * different account of what the measure's reading came to.
     */
    private static PositionAccount answeredFor() {
        return new PositionAccount("omitted", AT, Type.BOOL, ReadingResidue.NOTHING, ValueSet.ANY,
                new StructuralInspection.Continuation.None(), List.of(), List.of());
    }

    /** A position this compiler could not enter, which is what leaves a reading open. */
    private static PositionAccount notEntered() {
        return new PositionAccount("omitted", TermPath.of("r"), Type.BOOL,
                new ReadingResidue(new BlockedDescent(new BlockReason.ValueRulesNotReached()),
                        Set.of()),
                ValueSet.ANY, null, List.of(), List.of());
    }

    /** The one position above, under whatever the measures' readings came to. */
    private static List<UndividedPosition> undividedUnder(MeasureClosure.Both closure) {
        return new Partitions.Partitioning(
                List.of(new PositionMeasurements(answeredFor(), List.of(),
                        new BodyCutInspection.Exhausted())),
                List.of(), Set.of(), List.of(), List.of(), List.of(), Map.of(),
                ReachingCuts.NONE, closure.partition(), closure.border(), null)
                .undivided();
    }

    /** What a reading that was made came to, over the positions it was made over. */
    private static MeasureClosure.Both made(PositionAccount... over) {
        return MeasureClosure.of(List.of(over), List.of(), new LinesRead());
    }

    /**
     * A reading that ran out says the absence, which is what makes the row below a difference.
     *
     * <p>The control. Without it the law under it is met by a position that was never going to
     * reach an absence at all, and the whole file would be green over a reader that answers
     * one word everywhere.
     */
    @Test
    void aReadingThatRanOutSaysTheModelDividesItNoWay() {
        List<UndividedPosition> said = undividedUnder(made(answeredFor()));

        assertEquals(1, said.size(), said::toString);
        assertInstanceOf(UndividedPosition.Why.Absent.class, said.getFirst().why(),
                () -> "every rule about this position was read and none divides it: " + said);
    }

    /** And nothing about the model follows from the same position where nothing read the body. */
    @Test
    void aBodyNobodyReadSaysNothingAboutTheModel() {
        List<UndividedPosition> said = undividedUnder(
                MeasureClosure.bodyNotRead("omitted", made(answeredFor())));

        assertEquals(
                List.of(new UndividedPosition(AT, new UndividedPosition.Why.BodyNotInEvaluation())),
                said,
                "the rules the body writes were not among the ones that were read, so the model"
                        + " dividing this position no way is not what was established — and what"
                        + " it says instead is the body, not a reading that fell short here");
    }

    /**
     * And a reading that stopped on something it can name still answers for what it read.
     *
     * <p>The gap is at another position, which is what makes this row say something: the reading of
     * the position below was made and ran out, and the measure it is part of is short elsewhere.
     * Withheld here too, an author would be told a position nothing divides is underivable because
     * a different one could not be entered.
     */
    @Test
    void aReadingShortElsewhereStillAnswersForWhatItRead() {
        List<UndividedPosition> said = undividedUnder(made(answeredFor(), notEntered()));

        assertInstanceOf(MeasureClosure.OfThePartition.Open.class,
                made(answeredFor(), notEntered()).partition(),
                "this model is written so the partition measure's reading does not run out");
        assertEquals(1, said.size(), said::toString);
        assertInstanceOf(UndividedPosition.Why.Absent.class, said.getFirst().why(),
                () -> "what this position came to was read: " + said);
    }
}
