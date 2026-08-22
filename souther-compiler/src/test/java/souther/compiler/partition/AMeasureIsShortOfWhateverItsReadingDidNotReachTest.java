package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.BoundaryDerivation;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionDerivation;
import souther.compiler.query.PartitionEvidence;

import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A measure says it was made in full only where the reading it depends on ran out.
 *
 * <p>Held against sources, because every fact this is about is one a reading produces. A fixture
 * naming an answer and a test reading the name back is two spellings of one decision, and the step
 * being checked here is the one in between: what the reading came to, and what the measure makes of
 * it.
 *
 * <p>Both measures, and separately. What one of them is short of says nothing about the other, so a
 * model is written for each way of being short and the other measure's answer is asserted beside it.
 */
class AMeasureIsShortOfWhateverItsReadingDidNotReachTest {

    /**
     * Thirteen positions, one past {@link Partitions#MAX_AXES}, with a bound either side of the
     * limit.
     *
     * <p>The fields are in declaration order and the axes are drawn in it, so the thirteenth is the
     * one dropped. Two of them are {@code Amount}s on purpose: the twelfth's line survives and the
     * thirteenth's goes with the axis, which is what leaves the measure with a line to show and
     * short of one it cannot ask about. With only the dropped one bounded, the measure has nothing
     * to show and answers that it found no line rather than that it found some — a different
     * sentence, and one this model would not be about.
     */
    private static final String PAST_THE_LIMIT = """
            module example.limit

            data A
            data B
            data Flag = A | B
            data Amount = Int
                invariant value >= 0 && value <= 100
            data Wide = { f1: Flag, f2: Flag, f3: Flag, f4: Flag, f5: Flag, f6: Flag,
                          f7: Flag, f8: Flag, f9: Flag, f10: Flag, f11: Flag,
                          cost: Amount, extra: Amount }
            data Res = { n: Int }

            behavior wide : (w: Wide) -> Res
                constructs Res
            let wide (w) = Res { n = 1 }

            example wide
                | "one" : (Wide { f1 = A, f2 = A, f3 = A, f4 = A, f5 = A, f6 = A, f7 = A, f8 = A,
                                  f9 = A, f10 = A, f11 = A, cost = 1, extra = 1 })
                        -> Res { n = 1 }
            """;

    /**
     * The same twelve positions and no thirteenth, so nothing is dropped.
     *
     * <p>The control the model above needs. Without it, a border measure short of something would
     * be as good an account of a model this cannot read at all, and neither the limit nor the axis
     * past it would be what the first model shows.
     */
    private static final String WITHIN_THE_LIMIT = """
            module example.within

            data A
            data B
            data Flag = A | B
            data Amount = Int
                invariant value >= 0 && value <= 100
            data Narrow = { f1: Flag, f2: Flag, f3: Flag, f4: Flag, f5: Flag,
                            f6: Flag, f7: Flag, f8: Flag, f9: Flag, f10: Flag, f11: Flag,
                            cost: Amount }
            data Res = { n: Int }

            behavior narrow : (w: Narrow) -> Res
                constructs Res
            let narrow (w) = Res { n = 1 }

            example narrow
                | "one" : (Narrow { f1 = A, f2 = A, f3 = A, f4 = A, f5 = A, f6 = A, f7 = A, f8 = A,
                                    f9 = A, f10 = A, f11 = A, cost = 1 }) -> Res { n = 1 }
            """;

    /**
     * An axis dropped past the limit leaves both measures short of what it was carrying.
     *
     * <p>Not a report working out afterwards what the omission cost. What was carried is known where
     * the axis is dropped and nowhere else — neither a dropped classifier nor a dropped bound leaves
     * anything behind, so a reader counting entries afterwards sees a measure that was made and
     * found what there was.
     */
    @Test
    void anAxisDroppedPastTheLimitLeavesBothMeasuresShort() {
        PartitionEvidence wide = evidenceFor(PAST_THE_LIMIT, "wide");

        assertInstanceOf(BoundaryDerivation.Partial.class, wide.bounded());
        assertInstanceOf(PartitionDerivation.Partial.class, wide.partitioned());
    }

    /** And within the limit both are made in full, which is what says the answers above are the
     *  limit's and not the model's. */
    @Test
    void andWithinTheLimitBothAreMadeInFull() {
        PartitionEvidence narrow = evidenceFor(WITHIN_THE_LIMIT, "narrow");

        assertInstanceOf(BoundaryDerivation.Complete.class, narrow.bounded());
        assertInstanceOf(PartitionDerivation.Complete.class, narrow.partitioned());
    }

    private static PartitionEvidence evidenceFor(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.reportOnly());
        compilation.answerEverything();
        Map<String, PartitionEvidence> partitions = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        return partitions.get(behavior);
    }
}
