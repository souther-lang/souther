package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.function.ToLongFunction;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * An element's statement that also reads the total of its container is composed against the
 * container it is in, not against a container of that element alone: the elements are chosen
 * together with what the container comes to, so each is read against the total of the container
 * it stands in.
 */
class AStatementReadingTheWholeContainerIsComposedAgainstItsTotalTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String HEAD = """
            module probe

            data Forecast = { currency: String, amount: Int }

            behavior f : (fs: List<Forecast>) -> Int
            """;

    private static final String ELEMENTS = """
            let f (fs) = if List.length(List.filter(f ->
                f.amount * 2 > List.sum(List.map(.amount, fs)), fs)) == 1 then 1 else 0
            """;

    private static final String CURRENCIES = """
            let f (fs) = if Set.size(Set.fromList(List.map(.currency, List.filter(f ->
                f.amount * 2 > List.sum(List.map(.amount, fs)), fs)))) == 1 then 1 else 0
            """;

    /** An element above the total of the container by ten: one that no element meets in a
     *  container of itself alone. */
    private static final String ABOVE_THE_REST = """
            let f (fs) = if List.length(List.filter(f ->
                f.amount > List.sum(List.map(.amount, fs)) + 10, fs)) == 1 then 1 else 0
            """;

    private static final String COUNT_OF_ELEMENTS =
            "f/#fs [List.sum(fs[*].amount) - 2 * fs[*].amount < 0]";

    private static final String COUNT_OF_CURRENCIES = "f/#different fs [fs[*].currency] where"
            + " [List.sum(fs[*].amount) - 2 * fs[*].amount < 0]";

    private static final Pattern ELEMENT =
            Pattern.compile("currency = \"([^\"]*)\", amount = (-?\\d+)");

    /** An element of a row composed. */
    private record Forecast(String currency, int amount) {}

    private static Compilation measured(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList());
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList(),
                "every example answers what it writes");
        return compilation;
    }

    private static JsonNode line(Compilation compilation, String axis) {
        JsonNode report = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        for (JsonNode behavior : report.at("/modules/0/behaviors")) {
            for (JsonNode each : behavior.at("/partition/boundaries")) {
                if (axis.equals(each.path("axis").asString())) {
                    return each;
                }
            }
        }
        throw new AssertionError("a line on " + axis + ": " + report);
    }

    private static JsonNode pointAgainst(JsonNode line, String against) {
        for (JsonNode each : line.path("items")) {
            if (against.equals(each.path("against").asString())) {
                return each;
            }
        }
        throw new AssertionError("a point against " + against + " on " + line);
    }

    /** The elements of a row composed, as the amounts and currencies it writes. */
    private static List<Forecast> elementsOf(CharSequence row) {
        List<Forecast> out = new ArrayList<>();
        Matcher found = ELEMENT.matcher(row);
        while (found.find()) {
            out.add(new Forecast(found.group(1), Integer.parseInt(found.group(2))));
        }
        return out;
    }

    private static List<Forecast> meeting(List<Forecast> row) {
        int total = row.stream().mapToInt(Forecast::amount).sum();
        return row.stream().filter(each -> each.amount() * 2 > total).toList();
    }

    private static long elementsMeeting(List<Forecast> row) {
        return meeting(row).size();
    }

    private static long currenciesMeeting(List<Forecast> row) {
        return meeting(row).stream().map(Forecast::currency).distinct().count();
    }

    /** Every point of the line that a value can stand at has a row, as the elements of the
     *  container are chosen together. */
    private static void everyPointHasARow(String behavior, String axis) {
        JsonNode line = line(measured(HEAD + behavior), axis);
        assertFalse(line.path("items").isEmpty(), line::toString);
        for (JsonNode item : line.path("items")) {
            assertTrue(item.has("notOwed") || item.path("knownWritable").asBoolean(),
                    item::toString);
        }
    }

    /**
     * Each row composed is run as an example answering what the language computes of it, and
     * none is refused. The counts the rows hold are the ones the line is drawn at, so a row
     * composed against a container of its element alone, which holds another, is not among them.
     *
     * @return the number each row holds of what is counted
     */
    private static Set<Long> rowsComposedHold(String behavior, ToLongFunction<List<Forecast>> held) {
        Compilation compilation = measured(HEAD + behavior);
        String rows = GeneratedRows.of(compilation, "probe", null,
                SourceRendering.namedByIdentity(compilation.texts())).text();
        StringBuilder examples = new StringBuilder("\nexample f\n");
        StringBuilder row = new StringBuilder();
        Set<Long> counts = new HashSet<>();
        for (String text : rows.split("\n")) {
            if (text.startsWith("//")) {
                continue;
            }
            if (text.startsWith("    |")) {
                row = new StringBuilder();
            }
            row.append(text).append('\n');
            if (!text.contains("<?>")) {
                continue;
            }
            long count = held.applyAsLong(elementsOf(row));
            counts.add(count);
            examples.append(row.toString().replace("<?>", count == 1 ? "1" : "0"));
        }
        assertFalse(counts.isEmpty(), () -> "rows composed: " + rows);
        measured(HEAD + behavior + examples);
        return counts;
    }

    @Test
    void everyPointOfTheLineOnTheElementsMeetingItHasARow() {
        everyPointHasARow(ELEMENTS, COUNT_OF_ELEMENTS);
    }

    @Test
    void everyPointOfTheLineOnTheCurrenciesOfThoseMeetingItHasARow() {
        everyPointHasARow(CURRENCIES, COUNT_OF_CURRENCIES);
    }

    /**
     * The line is drawn at one, at nought, at two and past two, and a row is composed holding
     * each. Past two every element is above half of a total below nought, which an element read
     * against a total of itself alone is not.
     */
    @Test
    void theRowsComposedHoldTheCountOfElementsTheirPointsAsk() {
        Set<Long> counts = rowsComposedHold(ELEMENTS,
                AStatementReadingTheWholeContainerIsComposedAgainstItsTotalTest::elementsMeeting);
        assertTrue(counts.containsAll(List.of(0L, 1L, 2L)), counts::toString);
        assertTrue(counts.stream().anyMatch(count -> count > 2), counts::toString);
    }

    /** Where no element meets the statement in a container of itself alone, a row holding one is
     *  composed all the same: it is the total of the container that the element is above. */
    @Test
    void anElementAboveTheRestByTenIsComposedThoughNoneIsAboveItselfByTen() {
        Set<Long> counts = rowsComposedHold(ABOVE_THE_REST, row -> {
            int total = row.stream().mapToInt(Forecast::amount).sum();
            return row.stream().filter(each -> each.amount() > total + 10).count();
        });
        assertTrue(counts.contains(1L), counts::toString);
    }

    @Test
    void theRowsComposedHoldTheCountOfCurrenciesTheirPointsAsk() {
        Set<Long> counts = rowsComposedHold(CURRENCIES,
                AStatementReadingTheWholeContainerIsComposedAgainstItsTotalTest::currenciesMeeting);
        assertTrue(counts.containsAll(List.of(0L, 1L, 2L)), counts::toString);
        assertTrue(counts.stream().anyMatch(count -> count > 2), counts::toString);
    }

    /** A row that stands on the line is at the point of its count. */
    @Test
    void aRowHoldingSoManyAboveHalfTheTotalIsAtThePointOfThatCount() {
        String examples = """

                example f
                    | "none" : ([]) -> 0
                    | "one" : ([Forecast { currency = "USD", amount = 2 },
                        Forecast { currency = "USD", amount = 1 }]) -> 1
                    | "two" : ([Forecast { currency = "USD", amount = 4 },
                        Forecast { currency = "JPY", amount = 4 },
                        Forecast { currency = "EUR", amount = -3 }]) -> 0
                """;
        JsonNode line = line(measured(HEAD + ELEMENTS + examples), COUNT_OF_ELEMENTS);
        for (String against : List.of("1", "0", "2")) {
            assertTrue(pointAgainst(line, against).path("hit").asBoolean(),
                    () -> "a row at " + against + " in " + line);
        }
    }
}
