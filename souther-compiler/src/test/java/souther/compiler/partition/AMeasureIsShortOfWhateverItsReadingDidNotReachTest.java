package souther.compiler.partition;

import souther.compiler.query.Measurement;
import souther.compiler.report.AdequacyReport;
import org.junit.jupiter.api.Test;

import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
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
     * A position the walk could not reach into, which is a fact no question carries.
     *
     * <p>Nothing was read there and so nothing was found wanting: a {@code Map} holds its values
     * inside something this does not enter, and a rule about what is inside raises no question this
     * could be short of. Both measures are short of it, because what is not known about the
     * position is not known for either.
     *
     * <p><b>Written on a mapping because that is what is left.</b> This was an {@code Amount?}, and
     * an optional is entered now — what it holds stands at the narrowing that says it holds
     * something, where the rules of that type are read and its border is owed. So the model that
     * used to be short of both is short of one, and a fixture kept for its numbers would have gone
     * on being called a position nothing reached into.
     *
     * <p><b>The {@code Bool} is what makes the model say two things.</b> This is about the two
     * measures answering apart, and a position has to be measured for one of them to be the answer
     * it is: the optional divided into holding something and holding nothing and was that position
     * itself, and a mapping divides nothing. Without it both measures say the same word for
     * different reasons, and the test would pass over the two being merged. So the field is part of
     * what is being said and is asserted below rather than left standing as scenery.
     */
    private static final String RULES_NOT_REACHED = """
            module example.notreached

            data Amount = Int
                invariant value >= 0 && value <= 100
            data Req = { cost: Map<String, Amount>, flag: Bool }
            data Res = { n: Int }

            behavior f : (r: Req) -> Res
                constructs Res
            let f (r) = Res { n = 0 }

            example f
                | "one" : (Req { cost = [ ("a", Amount(1)) ], flag = true }) -> Res { n = 0 }
            """;

    /**
     * A rule this reading set aside that leaves neither measure short.
     *
     * <p>An order across a pair of positions divides neither of them, and the line it draws where
     * the two hold one count is not one an invariant places. So both measures answered everything
     * they answer for and found nothing — which is a fact about the model and not about this
     * compiler, and no row would change it.
     */
    private static final String SET_ASIDE_COSTING_NEITHER = """
            module example.relation

            data Span = { startsAt: Int, endsAt: Int }
                invariant startsAt <= endsAt
            data Res = { n: Int }

            behavior f : (v: Span) -> Res
                constructs Res
            let f (v) = Res { n = v.startsAt }

            example f
                | "one" : (Span { startsAt = 1, endsAt = 2 }) -> Res { n = 1 }
            """;

    /**
     * A position whose rules the walk never reached leaves both measures short.
     *
     * <p>The second of the three facts no question carries. It is not a rule read and found
     * wanting, so nothing about it stands among the questions — and a closure counted over the
     * questions alone would call this behavior read to the end.
     */
    @Test
    void aPositionTheWalkDidNotReachIntoLeavesBothMeasuresShort() {
        PartitionEvidence evidence = evidenceFor(RULES_NOT_REACHED, "f");
        souther.compiler.query.Measure<List<souther.compiler.query.BorderAssessment>> reading =
                readingFor(RULES_NOT_REACHED, "f");

        // What the partition did measure, so that the two answers below are one model saying two
        // things rather than one measure with nothing in it. A fixture whose every position is out
        // of reach says `NOT_MEASURED` on both sides for two different reasons, and reading that as
        // this would be the merge this exists to catch.
        assertEquals(List.of("r.flag"),
                evidence.axes().stream().map(PartitionEvidence.AxisCoverage::path).toList(),
                () -> "the mapping divides nothing, so the `Bool` is the position measured here");

        assertEquals(MeasurementStatus.PARTIAL, AdequacyReport.statusOf(evidence.partitioned()),
                () -> "partition: " + evidence.partitioned());
        assertEquals(MeasurementStatus.NOT_MEASURED, AdequacyReport.statusOf(reading),
                () -> "border: " + reading);
    }

    /**
     * And a rule set aside for what it says leaves neither measure short.
     *
     * <p>The third, and the one the other two would be read as if a refusal were counted rather
     * than asked. Neither measure is held open: the rule was read from end to end, and holding a
     * verdict open for it would be this compiler reporting a model whose every rule it understood.
     *
     * <p><b>Which is not the same as there being nothing to measure.</b> The rule divides neither
     * position, so the partition has no class to be about; it does say where the pair parts, so the
     * border has a line and answers in full. Read as one verdict for both, a model stating a
     * relation comes back as one stating nothing.
     */
    @Test
    void andARuleSetAsideForWhatItSaysLeavesNeither() {
        PartitionEvidence evidence = evidenceFor(SET_ASIDE_COSTING_NEITHER, "f");

        assertInstanceOf(Measurement.NotApplicable.class, evidence.partitioned());
        assertInstanceOf(Measurement.Complete.class, readingFor(SET_ASIDE_COSTING_NEITHER, "f"),
                "the relation is a line, and one read from end to end is measured in full");
        // And the rule is named beside them, so the two answers are about a model with a rule in it
        // and not about one with none.
        assertEquals(2, evidence.rulesWithoutALine().size(), () -> "unread: " + evidence.rulesWithoutALine());
    }

    private static PartitionEvidence evidenceFor(String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        Map<String, PartitionEvidence> partitions = compilation.db()
                .ask(new Adequacy.Coverage(compilation.modules().get(0))).value();
        return partitions.get(behavior);
    }

    /** How far the reading that found the behavior's lines got. */
    private static souther.compiler.query.Measure<
            List<souther.compiler.query.BorderAssessment>> readingFor(
            String source, String behavior) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return compilation.db()
                .ask(new Adequacy.BoundaryReadings(compilation.modules().get(0)))
                .value().get(behavior);
    }
}
