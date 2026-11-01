package souther.compiler.partition;

import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;
import java.util.concurrent.ConcurrentHashMap;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a search of a list written out finds is the first element its closure holds of: the closure
 * is applied from the first element until one holds, and what is found is one it holds of. A
 * comparison of the value found is read on each element, as the arm taken where that element is
 * the one found — where the closure holds of it and of none before it — and as what it is
 * compared with where it holds of none.
 */
class TheValueAFindAnswersIsTheFirstElementItsClosureHoldsOfTest {

    private static final Map<String, Compilation> MEASURED = new ConcurrentHashMap<>();

    private static final String MODEL = """
            module demo

            data Yes = { n: Int }
            data No = { n: Int }

            behavior f : (a: Int) -> Yes | No
            let f (a) = {
                let e = List.rangeInclusive(0, 10) |> List.map(n -> a + n)
                    |> List.find(x -> x >= %s) |> Option.withDefault(a)
                if %s then Yes { n = a } else No { n = a }
            }
            """;

    /** A comparison of the value found is read: nothing of it is left unread. */
    @Test
    void aComparisonOfTheValueFoundIsRead() {
        assertEquals(List.of(), notRead("3", "e >= 5"));
        assertEquals(List.of(), notRead("3", "Int.floorMod(e, 7) >= 1"));
    }

    /**
     * The value found is the first the closure holds of. {@code e == 105} where the first element
     * at or past a hundred is found holds only where {@code a} is a hundred and five: below it
     * the first is a hundred, or nothing is found and {@code e} is {@code a}. Were it any element
     * the closure holds of, a row from ninety-five up would meet it. Each line on {@code a} is the
     * comparison's at a hundred and five or the closure's on an element, from ninety to a hundred.
     */
    @Test
    void theValueFoundIsTheFirstTheClosureHoldsOf() {
        Set<Long> lines = linesOnA("100", "e == 105");
        assertTrue(lines.contains(105L), lines::toString);
        Set<Long> drawn = new TreeSet<>(lines);
        drawn.removeIf(at -> at == 105L || (at >= 90L && at <= 100L));
        assertEquals(Set.of(), drawn, lines::toString);
    }

    /** The comparison on each element is a line a row is asked to stand at, and rows stand there:
     *  {@code e >= 5} holds where {@code a} is at least five. */
    @Test
    void aLineOnTheValueFoundIsALineOnTheInput() {
        assertTrue(linesOnA("3", "e >= 5").contains(5L));
    }

    /** The lines of {@code f} on {@code a}, each at the number it is drawn at. */
    private static Set<Long> linesOnA(String atLeast, String comparison) {
        Set<Long> out = new TreeSet<>();
        for (BorderAssessment line : Adequacy.readingsOf(
                measured(MODEL.formatted(atLeast, comparison)).db(), "demo").get("f")) {
            if (line.left().equals("a")) {
                out.add(Long.parseLong(line.value()));
            }
        }
        return out;
    }

    /** The rules of {@code f} said not read, each as its position and reason. */
    private static List<String> notRead(String atLeast, String comparison) {
        Compilation compilation = measured(MODEL.formatted(atLeast, comparison));
        JsonNode document = JsonMapper.builder().build().readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        List<String> out = new ArrayList<>();
        for (JsonNode each : document.findParents("partition")) {
            for (JsonNode entry : each.get("partition").get("notRead")) {
                out.add(entry.get("position").asString() + " " + entry.get("reason").asString());
            }
        }
        return out;
    }

    /** And given back when the class is done with them: a fork keeps its JVM. */
    @AfterAll
    static void released() {
        MEASURED.clear();
    }

    private static Compilation measured(String model) {
        return MEASURED.computeIfAbsent(model, source -> {
            Compilation compilation = Compilation.ofSource(source, "Main");
            compilation.measure(Adequacy.Asked.fullReport());
            compilation.answerEverything();
            assertEquals(List.of(), compilation.errors(), source);
            return compilation;
        });
    }
}
