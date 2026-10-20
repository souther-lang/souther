package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.InteractionEvidence;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The total the issue is about, written three ways, in the guard it was reported in.
 *
 * <p>The reading of a body is only part of what a measure is: the combinations are held to the way
 * to the guard a run goes, and a requirement is met by a run that did all of some one way of it. A
 * total written as a list or as a filter has to be asked of the rows exactly as the same two choices
 * added are, in the same count, to the same measure, with the same combinations unmade — and made by
 * the same rows.
 */
class TheSameTotalInAGuardIsAskedTheSameWhicheverWayItIsWrittenTest {

    private static final String A = "if w.first.days >= 17 then w.first.pay else 0";

    private static final String B = "if w.second.days >= 17 then w.second.pay else 0";

    private static final Map<String, String> WAYS = new LinkedHashMap<>();

    static {
        WAYS.put("two choices added", "(" + A + ") + (" + B + ")");
        WAYS.put("a list of the choices", "List.sum([ " + A + ", " + B + " ])");
        WAYS.put("a filter",
                "List.sum(List.map(r -> r.pay, List.filter(r -> r.days >= 17,"
                        + " [ w.first, w.second ])))");
        WAYS.put("a closure that chooses",
                "List.sum(List.map(r -> if r.days >= 17 then r.pay else 0, [ w.first, w.second ]))");
    }

    private static String model(String total, String rows) {
        return """
                module example.threshold

                data Month = { pay: Int, days: Int }
                data Win = { first: Month, second: Month }
                data Ok
                data No

                behavior f : (w: Win) -> Ok | No

                let f (w) = {
                    guard %s >= 900 else No
                    Ok
                }

                example f
                %s""".formatted(total, rows);
    }

    private static final String FIRST_ONLY =
            "    | (Win { first = Month { pay = 1000, days = 20 },"
                    + " second = Month { pay = 500, days = 5 } }) -> Ok\n";

    private static final String SECOND_ONLY =
            "    | (Win { first = Month { pay = 1000, days = 5 },"
                    + " second = Month { pay = 1000, days = 20 } }) -> Ok\n";

    private static final String BOTH =
            "    | (Win { first = Month { pay = 500, days = 20 },"
                    + " second = Month { pay = 500, days = 20 } }) -> Ok\n";

    private static final String NEITHER =
            "    | (Win { first = Month { pay = 1000, days = 5 },"
                    + " second = Month { pay = 1000, days = 5 } }) -> No\n";

    private static AdequacyReport.BehaviorReport behaviorOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return AdequacyReport.of(compilation).modules().getFirst().behaviors().getFirst();
    }

    /** What is asked of the rows: how many combinations, and whether any went unread. */
    private record Asked(int combinations, int read, int notPlaced, int notMeasured,
                         int notJoined, MeasurementStatus status) {

        static Asked of(AdequacyReport.BehaviorReport behavior) {
            InteractionEvidence evidence = behavior.evidence().interaction();
            return new Asked(evidence.counted(), evidence.asked().read(),
                    evidence.asked().notPlaced().size(), evidence.asked().notMeasured().size(),
                    evidence.asked().notJoined(), behavior.status());
        }
    }

    @Test
    void everyWayIsAskedForTheSameCombinationsUnderTheSameMeasure() {
        Asked first = null;
        for (Map.Entry<String, String> way : WAYS.entrySet()) {
            Asked asked = Asked.of(behaviorOf(model(way.getValue(), FIRST_ONLY)));
            assertTrue(asked.combinations() > 0, way.getKey() + " is asked for combinations");
            if (first == null) {
                first = asked;
            }
            assertEquals(first, asked, way.getKey());
        }
    }

    @Test
    void everyWayIsMetByTheSameRows() {
        List<String> rowSets = List.of(FIRST_ONLY, FIRST_ONLY + SECOND_ONLY,
                FIRST_ONLY + SECOND_ONLY + BOTH + NEITHER);
        for (String rows : rowSets) {
            Integer made = null;
            Integer unmade = null;
            for (Map.Entry<String, String> way : WAYS.entrySet()) {
                InteractionEvidence evidence =
                        behaviorOf(model(way.getValue(), rows)).evidence().interaction();
                int met = evidence.made().made().orElseThrow().met().size();
                made = made == null ? met : made;
                unmade = unmade == null ? evidence.notMadeByRows().size() : unmade;
                assertEquals(made, met, way.getKey() + " under " + rows);
                assertEquals(unmade, evidence.notMadeByRows().size(),
                        way.getKey() + " under " + rows);
            }
        }
    }
}
