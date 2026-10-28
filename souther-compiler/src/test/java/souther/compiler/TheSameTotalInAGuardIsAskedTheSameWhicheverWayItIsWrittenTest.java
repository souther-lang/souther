package souther.compiler;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.InteractionEvidence;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.stream.Collectors;

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

    /**
     * Each way, measured once over two rows, which every test here reads and none changes.
     *
     * <p>Two rows, the one choice taken and then the other, so that some combinations are made by
     * the rows and some are not: what is asked is that every way makes the same ones, and rows that
     * made all of them or none would leave half of that unasked.
     */
    private static final Map<String, AdequacyReport.BehaviorReport> MEASURED =
            new LinkedHashMap<>();

    private static AdequacyReport.BehaviorReport measured(String way) {
        return MEASURED.computeIfAbsent(way, each -> {
            Compilation compilation = Compilation.ofSource(
                    model(WAYS.get(each), FIRST_ONLY + SECOND_ONLY), "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            return AdequacyReport.of(compilation).modules().getFirst().behaviors().getFirst();
        });
    }

    /** And given back when the class is done with them: a fork keeps its JVM, so what is held
     *  statically is held for every class after this one. */
    @AfterAll
    static void released() {
        MEASURED.clear();
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
        for (String way : WAYS.keySet()) {
            Asked asked = Asked.of(measured(way));
            assertTrue(asked.combinations() > 0, way + " is asked for combinations");
            if (first == null) {
                first = asked;
            }
            assertEquals(first, asked, way);
        }
    }

    @Test
    void everyWayIsMetByTheSameRows() {
        Integer made = null;
        Integer unmade = null;
        for (String way : WAYS.keySet()) {
            InteractionEvidence evidence = measured(way).evidence().interaction();
            int met = evidence.made().made().orElseThrow().met().size();
            made = made == null ? met : made;
            unmade = unmade == null ? evidence.notMadeByRows().size() : unmade;
            assertEquals(made, met, way);
            assertEquals(unmade, evidence.notMadeByRows().size(), way);
        }
        assertTrue(made > 0 && unmade > 0,
                "the rows make some combinations and leave some unmade: " + made + " / " + unmade);
    }

    /** The lines of a report that say which values a total draws its borders at. */
    private static Set<String> bordersRead(String total) {
        Compilation compilation = Compilation.ofSource(
                model(total, FIRST_ONLY + SECOND_ONLY), "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        return report.lines().map(String::strip).filter(line -> line.startsWith("· read as"))
                .collect(Collectors.toCollection(TreeSet::new));
    }

    /**
     * What stands around the choice in the closure's body is read as it is written: the choice
     * alone is what an arm stands for. With a hundred added to the choice or twice the choice, the
     * borders are those of the same two months written out, a hundred and two hundred lower than
     * the threshold or half of it — and the same closure applied to the second month takes its own
     * arm.
     *
     * <p>Neither is read to the end. A choice is expanded into a relation for each arm, which
     * carries none of the operations the comparison works out, and a total over a closure is a
     * number worked out by a run that may stop and that no operation tells of. What is held is
     * that the closure draws no border the months written out do not.
     */
    @Test
    void aChoiceInAClosureIsReadWithWhatStandsAroundIt() {
        for (String body : List.of("(if R.days >= 17 then R.pay else 0) + 100",
                "2 * (if R.days >= 17 then R.pay else 0)")) {
            String closure = "List.sum(List.map(r -> " + body.replace("R", "r")
                    + ", [ w.first, w.second ]))";
            String written = "(" + body.replace("R", "w.first") + ") + ("
                    + body.replace("R", "w.second") + ")";
            Set<String> borders = bordersRead(written);
            assertTrue(borders.size() > 4, "the written form draws its borders: " + borders);
            Set<String> ofTheClosure = bordersRead(closure);
            assertTrue(borders.containsAll(ofTheClosure), body + "\n" + ofTheClosure);
        }
    }
}
