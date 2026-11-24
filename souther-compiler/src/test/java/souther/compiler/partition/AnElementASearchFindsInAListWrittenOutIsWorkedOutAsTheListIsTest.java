package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.ACompiledModel;
import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What a search finds in a list written out is worked out as the list is: a run builds every
 * element before the search looks at any, so what working an element out may stop a run at is
 * told of the comparison that reads the one found, and of the membership that decides which one
 * it is.
 *
 * <p>A date moved by a number written down stops only where the calendar does, which is no line
 * the model draws, so a comparison of the date found is read over every value; and where the run
 * may stop there before the membership deciding which one is found, the membership is not shown
 * at every value of the places it reads, and is not read of them for that reason alone.
 */
class AnElementASearchFindsInAListWrittenOutIsWorkedOutAsTheListIsTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** What the membership does over the rows that get to it is not shown at every value: the
     *  reason for every place not read here. */
    private static final String NOT_SHOWN = "relation_not_shown_to_reach_every_value";

    /** Each place the report says something was not read of, and the reasons it gives. */
    private static Map<String, Set<String>> unread(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        ACompiledModel.compiles(compilation);
        Map<String, Set<String>> out = new TreeMap<>();
        collect(JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE))), out);
        return out;
    }

    private static void collect(JsonNode node, Map<String, Set<String>> out) {
        if (node.isObject() && node.has("ruleId") && node.has("reason")
                && node.has("position") && !node.path("reason").asString().startsWith("rule_")) {
            out.computeIfAbsent(node.path("position").asString(), _ -> new TreeSet<>())
                    .add(node.path("reason").asString());
        }
        node.forEach(child -> collect(child, out));
    }

    /** The day after, where it is no holiday, and the day itself otherwise. */
    @Test
    void aDateFoundAmongDatesMovedByANumberWrittenDownIsReadOverEveryValue() {
        assertEquals(Map.of(), unread("""
                module demo

                behavior f : (s: Date, holidays: Set<Date>, from: Date) -> Bool

                let f (s, holidays, from) =
                    Int.floorMod(Date.daysBetween(s, Option.withDefault(from,
                        List.find(c -> Bool.not(Set.contains(c, holidays)),
                            [Date.addDays(1, from)]))), 7) >= 1
                """));
    }

    /**
     * Found as the first of two, the date is the day itself, and the run has worked out the day
     * after as well: at the last day of the calendar it stops there. That is the membership's own
     * arithmetic, which draws no line: the day and the holidays are the places the membership is
     * not shown at every value of, and nothing else is not read.
     */
    @Test
    void anElementTheComparisonDoesNotReadIsAStopOnTheWayAndNoLine() {
        String model = """
                module demo

                behavior f : (s: Date, holidays: Set<Date>, from: Date) -> Bool

                let f (s, holidays, from) =
                    Int.floorMod(Date.daysBetween(s, Option.withDefault(from,
                        List.find(c -> Bool.not(Set.contains(c, holidays)),
                            [from, Date.addDays(1, from)]))), 7) >= 1
                """;
        assertEquals(Map.of("from", Set.of(NOT_SHOWN), "holidays[*]", Set.of(NOT_SHOWN)),
                unread(model));
    }

    /**
     * Found as the third of three, the two before it are holidays and the third is not: two
     * elements of the calendar are the first two days, and every element is another day than the
     * third, which those two are. Read as they are, the comparison draws no line, and the places
     * the membership is not shown at every value of are the day and the holidays only.
     */
    @Test
    void theHolidaysBeforeTheOneFoundAreElementsApartFromIt() {
        String model = """
                module demo

                behavior f : (s: Date, holidays: Set<Date>, from: Date) -> Bool

                let f (s, holidays, from) =
                    Int.floorMod(Date.daysBetween(s, Option.withDefault(from,
                        List.find(c -> Bool.not(Set.contains(c, holidays)),
                            [from, Date.addDays(1, from), Date.addDays(2, from)]))), 7) >= 1
                """;
        assertEquals(Map.of("from", Set.of(NOT_SHOWN), "holidays[*]", Set.of(NOT_SHOWN)),
                unread(model));
    }
}
