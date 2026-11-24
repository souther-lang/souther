package souther.compiler;

import org.junit.jupiter.api.Test;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Weakening;
import souther.compiler.report.AdequacyReport;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Elements of a list that different arms of one {@code match} write out are kept by one decision,
 * of which exactly one arm is taken on a run. Counting them is no meeting of decisions, and it is
 * not a meeting that could not be joined.
 */
class ElementsKeptByArmsOfOneChoiceAreOneDecisionTest {

    @Test
    void aCountOfWhatTwoArmsOfOneMatchWriteIsNoMeeting() {
        AdequacyReport.BehaviorReport behavior = behaviorOf("""
                module m20

                data EmailOnly = { email: String }
                data Both = { email: String, phone: String }
                data PhoneOnly = { phone: String }
                data Reach = EmailOnly | Both | PhoneOnly

                let emailOf (r: Reach): List<String> =
                    match r with
                        | EmailOnly { email } -> [ email ]
                        | Both { email }      -> [ email ]
                        | PhoneOnly           -> []

                behavior hasEmail : (r: Reach) -> Bool
                let hasEmail (r) = List.length(emailOf(r)) >= 1

                example hasEmail
                    | "email" : (EmailOnly { email = "a" }) -> true
                    | "both" : (Both { email = "a", phone = "p" }) -> true
                    | "phone" : (PhoneOnly { phone = "p" }) -> false
                """);

        assertEquals(List.of(), behavior.evidence().interaction().asked().notJoined(),
                "one match is one decision, so there is nothing that was not joined");
        assertFalse(behavior.weakenedBy().causes().stream()
                        .anyMatch(Weakening.MeetingsNotJoined.class::isInstance),
                () -> "and nothing is said to have gone unjoined: " + behavior.weakenedBy());
        assertEquals(MeasurementStatus.COMPLETE, behavior.status(),
                () -> "so the measure is whole: " + behavior.weakenedBy());
    }

    /**
     * One {@code match} evaluated for two values is two decisions: a run takes an arm for each. They
     * are not one because they are written once, so the count of what they write is a meeting that
     * is said and not one that vanishes.
     */
    @Test
    void aCountOfWhatOneMatchWritesForTwoValuesIsStillAMeeting() {
        AdequacyReport.BehaviorReport behavior = behaviorOf("""
                module m22

                data EmailOnly = { email: String }
                data PhoneOnly = { phone: String }
                data Reach = EmailOnly | PhoneOnly

                let emailOf (r: Reach): List<String> =
                    match r with
                        | EmailOnly { email } -> [ email ]
                        | PhoneOnly           -> []

                behavior both : (a: Reach, b: Reach) -> Int
                let both (a, b) = List.length(emailOf(a) ++ emailOf(b))

                example both
                    | (EmailOnly { email = "x" }, PhoneOnly { phone = "p" }) -> 1
                """);

        assertEquals(1, behavior.evidence().interaction().asked().read(),
                "the two matches are two decisions that meet in the count");
    }

    @Test
    void aCountOfWhatTwoDifferentMatchesWriteIsStillAMeetingNotJoined() {
        AdequacyReport.BehaviorReport behavior = behaviorOf("""
                module m21

                data Reach = Email | Phone | Both

                let emailOf (r: Reach): List<String> =
                    match r with
                        | Email -> [ "e" ]
                        | Both  -> [ "e" ]
                        | Phone -> []

                let phoneOf (r: Reach): List<String> =
                    match r with
                        | Phone -> [ "p" ]
                        | Both  -> [ "p" ]
                        | Email -> []

                behavior channels : (r: Reach) -> Int
                let channels (r) = List.length(emailOf(r) ++ phoneOf(r))

                example channels
                    | "email" : (Email) -> 1
                    | "phone" : (Phone) -> 1
                    | "both" : (Both) -> 2
                """);

        assertTrue(behavior.evidence().interaction().asked().read() >= 1,
                "two matches are two decisions that meet in the count");
    }

    private static AdequacyReport.BehaviorReport behaviorOf(String model) {
        Compilation compilation = ACompiledModel.measured(model, Adequacy.Asked.fullReport());
        return AdequacyReport.of(compilation).modules().getFirst().behaviors().getFirst();
    }
}
