package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Weakening;
import souther.compiler.report.AdequacyReport;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether decisions meet is a fact of the body, and what a row has to do to be seen making a
 * combination of them is another. A meeting where no way in can be stated — under the arms of an
 * attempt, whose arm is taken by whether a value could be built — is a meeting still, and the
 * measure says it went without it rather than calling itself whole.
 */
class AMeetingNoWayInCanBeStatedForIsSaidAndNotDroppedTest {

    @Test
    void aMeetingInTheArmOfAnAttemptIsSaidNotToHaveBeenOffered() {
        Compilation compilation = ACompiledModel.measured("""
                module example.attempt

                data Small = { n: Int }
                    invariant n >= 0

                behavior f : (x: Int, y: Int, a: Int) -> Int
                let f (x, y, a) =
                    if Small { n = a } as small
                    then (if x > 1 then 1 else 2) + (if y > 1 then 10 else 20)
                    else 0

                example f
                    | (0, 0, 1) -> 22
                    | (0, 0, -1) -> 0
                """, Adequacy.Asked.fullReport());
        AdequacyReport.BehaviorReport behavior = AdequacyReport.of(compilation).modules().getFirst()
                .behaviors().getFirst();

        assertTrue(behavior.weakenedBy().causes().stream()
                        .anyMatch(Weakening.MeetingsNotJoined.class::isInstance),
                () -> "the meeting under the attempt is said: " + behavior.weakenedBy());
        assertEquals(MeasurementStatus.PARTIAL, behavior.status(),
                () -> "so the measure is not called whole: " + behavior.weakenedBy());
    }
}
