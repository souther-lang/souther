package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * How many different values a walk ends with that adds to what it carried every element of a set
 * inside each element ({@link souther.compiler.meaning.Quantity.HowManyDifferentAcross}) is read
 * only where the step's operation has a law of how many its answer holds and a law of which
 * values those are. That the number read is what the language computes is held in {@code
 * partition.ANumberReadOffABodyIsWhatTheBodyComputesTest}.
 *
 * <p>A union has both: its law of how many counts what the second set adds to the first, and its
 * law of membership says the answer holds exactly the values either set held.
 */
class HowManyDifferentValuesAWalkGathersAcrossItsElementsIsReadTest {

    private static final String HEAD = """
            module probe.across

            data ContactId = String
            data Attendees = Set<ContactId>
            data Meeting = { minutes: Int, attendees: Attendees }
            data Mixed = { n: Int }

            """;

    private static List<String> notRead(String behavior, String name) {
        Compilation compilation = Compilation.ofSource(HEAD + behavior, "Main");
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList());
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        List<String> said = new ArrayList<>();
        for (AdequacyReport.BehaviorReport each :
                AdequacyReport.of(compilation).modules().get(0).behaviors()) {
            if (each.name().equals(name)) {
                each.partition().notRead().forEach(one -> said.add(one.at() + " " + one.reason()));
            }
        }
        return said.stream().sorted().toList();
    }

    /** The values the sets hold are related among themselves, and nothing is left of a value
     *  worked out of them. */
    @Test
    void howManyPeopleTheMeetingsHadIsReadAsTheValuesTheirSetsHold() {
        assertEquals(List.of("meetings[*].attendees[*] RULE_RELATING_TWO_VALUES"), notRead("""
                behavior f : (meetings: List<Meeting>) -> Int | Mixed
                let f (meetings) = {
                    let everyone: Set<ContactId> =
                        List.fold((acc, m) -> Set.union(acc, m.attendees.value), Set.empty,
                                  meetings)
                    guard Set.size(everyone) <= 1 else Mixed { n = Set.size(everyone) }
                    1
                }
                """, "f"));
    }

    /**
     * A union's law counts what its second argument adds to its first, so a walk carrying its
     * answer in the second is no walk this reads: that the two may be swapped is stated nowhere.
     * And one adding a set that is no element's is no number of the elements.
     */
    @Test
    void aWalkThatIsNotTheElementsSetsAddedToWhatItCarriedIsNotReadSo() {
        assertEquals(List.of("meetings RULE_ABOUT_A_DERIVED_VALUE",
                "meetings[*].attendees RULE_ABOUT_A_DERIVED_VALUE"), notRead("""
                behavior f : (meetings: List<Meeting>) -> Bool
                let f (meetings) = Set.size(List.fold((acc, m) -> Set.union(m.attendees.value, acc),
                    Set.empty, meetings)) <= 1
                """, "f"));
        assertEquals(List.of("meetings RULE_ABOUT_A_DERIVED_VALUE",
                "meetings[*].attendees RULE_ABOUT_A_DERIVED_VALUE"), notRead("""
                behavior f : (meetings: List<Meeting>) -> Bool
                let f (meetings) = Set.size(List.fold(
                    (acc, m) -> Set.union(m.attendees.value, m.attendees.value), Set.empty,
                    meetings)) <= 1
                """, "f"));
        assertEquals(List.of("meetings RULE_ABOUT_A_DERIVED_VALUE",
                "others RULE_ABOUT_A_DERIVED_VALUE"), notRead("""
                behavior f : (meetings: List<Meeting>, others: Attendees) -> Bool
                let f (meetings, others) = Set.size(List.fold(
                    (acc, m) -> Set.union(acc, others.value), Set.empty, meetings)) <= 1
                """, "f"));
    }

}
