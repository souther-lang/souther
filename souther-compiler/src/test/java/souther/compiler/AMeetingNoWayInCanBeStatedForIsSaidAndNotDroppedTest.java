package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Weakening;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether decisions meet is a fact of the body, and what a row has to do to be seen making a
 * combination of them is another. A meeting where no way in can be stated — under the arms of an
 * attempt, whose arm is taken by whether a value could be built — is a meeting still: its
 * combinations are asked of the rows by what the rows are seen doing at its decisions, and the
 * ones no row made are not known to be makeable, which the measure says.
 */
class AMeetingNoWayInCanBeStatedForIsSaidAndNotDroppedTest {

    private static final String ATTEMPT = """
            module example.attempt

            data Small = { n: Int }
                invariant n >= 0

            behavior f : (x: Int, y: Int, a: Int) -> Int
            let f (x, y, a) =
                if Small { n = a } as small
                then (if x > 1 then 1 else 2) + (if y > 1 then 10 else 20)
                else 0

            """;

    private static AdequacyReport.BehaviorReport measured(String examples) {
        Compilation compilation = ACompiledModel.measured(ATTEMPT + examples, Adequacy.Asked.fullReport());
        return AdequacyReport.of(compilation).modules().getFirst().behaviors().getFirst();
    }

    @Test
    void aMeetingInTheArmOfAnAttemptIsOfferedAndItsUnmadeCombinationsAreUndetermined() {
        AdequacyReport.BehaviorReport behavior = measured("""
                example f
                    | (0, 0, 1) -> 22
                    | (0, 0, -1) -> 0
                """);

        assertTrue(behavior.weakenedBy().causes().stream()
                        .anyMatch(Weakening.MeetingsExistenceUndetermined.class::isInstance),
                () -> "the combinations no row made are not known to exist: " + behavior.weakenedBy());
        assertFalse(behavior.weakenedBy().causes().stream()
                        .anyMatch(Weakening.MeetingsNotJoined.class::isInstance),
                () -> "the meeting is offered, not left out: " + behavior.weakenedBy());
        assertEquals(MeasurementStatus.PARTIAL, behavior.status(),
                () -> "so the measure is not called whole: " + behavior.weakenedBy());
    }

    @Test
    void rowsThatMakeEveryCombinationOfAMeetingInTheArmOfAnAttemptLeaveNothingUndetermined() {
        AdequacyReport.BehaviorReport behavior = measured("""
                example f
                    | (0, 0, 1) -> 22
                    | (2, 0, 1) -> 21
                    | (0, 2, 1) -> 12
                    | (2, 2, 1) -> 11
                    | (0, 0, -1) -> 0
                """);

        assertFalse(behavior.weakenedBy().causes().stream()
                        .anyMatch(Weakening.MeetingsExistenceUndetermined.class::isInstance),
                () -> "every combination was made: " + behavior.weakenedBy());
        assertFalse(behavior.weakenedBy().causes().stream()
                        .anyMatch(Weakening.MeetingsNotJoined.class::isInstance),
                () -> "the meeting is offered: " + behavior.weakenedBy());
    }
}
