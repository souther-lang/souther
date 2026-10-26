package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;

/**
 * An operator every row the declarations leave gets past ties no places, and a relation reached
 * after it is reached at every value.
 *
 * <p>The difference of two years cannot pass either end of an {@code Int}, because a year has a
 * least and a greatest and the difference stays between them. Left as a condition on a pair of
 * dates, a comparison worked out after it was said to be reached at no value of either — the run
 * might stop on the subtraction — which no row does. Two plain {@code Int}s are not so bounded,
 * and their difference is.
 */
class AnOperatorThatEveryRowPassesStopsNoRunOnItsPlacesTest {

    private static PartitionEvidence measured(String parameters, String body) {
        Compilation compilation = Compilation.ofSource("""
                module probe

                behavior f : (%s) -> Bool

                let f (%s) = %s
                """.formatted(parameters, names(parameters), body), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        PartitionEvidence evidence = compilation.db()
                .ask(new Adequacy.Coverage("probe")).value().get("f");
        assertNotNull(evidence, "the model under test compiles");
        return evidence;
    }

    private static String names(String parameters) {
        return String.join(", ", java.util.Arrays.stream(parameters.split(","))
                .map(each -> each.substring(0, each.indexOf(':')).trim()).toList());
    }

    private static List<String> notReachedAtEveryValue(PartitionEvidence evidence) {
        return evidence.notRead().stream()
                .filter(each -> each.reason()
                        == UndividedPosition.Reason.RELATION_NOT_SHOWN_REACHED_AT_EVERY_VALUE)
                .map(PartitionEvidence.NotRead::at).sorted().distinct().toList();
    }

    @Test
    void theDifferenceOfTwoYearsStopsNoRunOnTheMonthsAfterIt() {
        PartitionEvidence evidence = measured("birthday: Date, today: Date", """
                Date.year(today) - Date.year(birthday)
                    - (if Date.month(today) < Date.month(birthday) then 1 else 0) >= 18""");

        assertEquals(List.of(), notReachedAtEveryValue(evidence),
                () -> evidence.notRead().toString());
    }

    /** The measure is complete: the stop was the only thing keeping it from being. */
    @Test
    void theMeasureOfTheAgeOfSomebodyBornOnADateIsComplete() {
        PartitionEvidence evidence = measured("birthday: Date, today: Date", """
                Date.year(today) - Date.year(birthday)
                    - (if Date.month(today) * 100 + Date.day(today)
                           < Date.month(birthday) * 100 + Date.day(birthday)
                       then 1 else 0) >= 18""");

        assertEquals(List.of(), notReachedAtEveryValue(evidence),
                () -> evidence.notRead().toString());
        assertEquals(List.of(), evidence.notRead().stream()
                .filter(PartitionEvidence.NotRead::readingStopped)
                .map(PartitionEvidence.NotRead::at).toList());
    }
}
