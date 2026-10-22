package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * How many different values a walk ends with that adds to what it carried every element of a set
 * inside each element ({@link souther.compiler.meaning.Quantity.HowManyDifferentAcross}) is read
 * off the law of how many the step's operation answers, and is what the language computes.
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

    private record Case(String says, List<Set<String>> meetings) {}

    private static int counted(List<Set<String>> meetings) {
        Set<String> all = new HashSet<>();
        meetings.forEach(all::addAll);
        return all.size();
    }

    private static final List<Case> CASES = List.of(
            new Case("no meeting", List.of()),
            new Case("one meeting of one", List.of(Set.of("a"))),
            new Case("one meeting of two", List.of(Set.of("a", "b"))),
            new Case("two meetings of the same one", List.of(Set.of("a"), Set.of("a"))),
            new Case("two meetings sharing one", List.of(Set.of("a", "b"), Set.of("b", "c"))),
            new Case("three meetings of different ones",
                    List.of(Set.of("a"), Set.of("b"), Set.of("c"))));

    /** The language answers, for each case, the number of values across every set. */
    @Test
    void theLanguageAnswersHowManyDifferAcrossEverySet() {
        StringBuilder source = new StringBuilder(HEAD + """
                behavior people : (meetings: List<Meeting>) -> Int
                let people (meetings) = Set.size(List.fold(
                    (acc, m) -> Set.union(acc, m.attendees.value), Set.empty, meetings))

                example people
                """);
        for (Case each : CASES) {
            List<String> written = new ArrayList<>();
            for (Set<String> one : each.meetings()) {
                written.add("Meeting { minutes = 30, attendees = Attendees(Set.fromList(["
                        + String.join(", ", one.stream().sorted()
                                .map(name -> "ContactId(\"" + name + "\")").toList())
                        + "])) }");
            }
            source.append("    | \"").append(each.says()).append("\" : ([")
                    .append(String.join(", ", written)).append("]) -> ")
                    .append(counted(each.meetings())).append('\n');
        }
        Compilation compilation = Compilation.ofSource(source.toString(), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList());
        assertEquals(List.of(0, 1, 2, 1, 3, 3),
                CASES.stream().map(each -> counted(each.meetings())).toList());
    }
}
