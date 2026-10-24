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
import java.util.function.Consumer;
import java.util.function.ToIntFunction;
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
 *
 * <p>Each row composed is run as an example answering what the language computes of it, and none
 * is refused: a row composed against a container of its element alone holds another count than
 * the point it was composed for.
 */
class AStatementReadingTheWholeContainerIsComposedAgainstItsTotalTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String PLAIN = "data Forecast = { currency: String, amount: Int }\n";

    private static final String HALF = "f.amount * 2 > List.sum(List.map(.amount, fs))";

    private static final Pattern ELEMENT = Pattern.compile(
            "currency = \"([^\"]*)\", amount = (-?\\d+)(?:, active = (true|false))?");

    private static final Pattern BESIDE = Pattern.compile("\\(\\s*(-?\\d+)\\s*,\\s*\\[");

    /** An element of a row composed. */
    private record Forecast(String currency, int amount, boolean active) {}

    /** A row composed: the number beside the list, where there is one, and the list. */
    private record Row(int k, List<Forecast> elements) {

        int total() {
            return elements.stream().mapToInt(Forecast::amount).sum();
        }

        long countOf(java.util.function.Predicate<Forecast> meets) {
            return elements.stream().filter(meets).count();
        }
    }

    /** The parameters of the behavior, as declared and as named where it is defined. */
    private record Parameters(String declared, String named) {}

    private static final Parameters FS = new Parameters("fs: List<Forecast>", "fs");

    private static final Parameters K_AND_FS =
            new Parameters("k: Int, fs: List<Forecast>", "k, fs");

    private static String source(String data, Parameters parameters, String body) {
        return "module probe\n\n" + data + "\nbehavior f : (" + parameters.declared()
                + ") -> Int\nlet f (" + parameters.named() + ") = " + body + "\n";
    }

    private static String listCount(String statement) {
        return "List.length(List.filter(f -> " + statement + ", fs))";
    }

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

    private static JsonNode lines(Compilation compilation) {
        return JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
    }

    private static List<JsonNode> countLines(Compilation compilation) {
        List<JsonNode> out = new ArrayList<>();
        for (JsonNode behavior : lines(compilation).at("/modules/0/behaviors")) {
            for (JsonNode each : behavior.at("/partition/boundaries")) {
                if (each.path("axis").asString().startsWith("f/#")) {
                    out.add(each);
                }
            }
        }
        return out;
    }

    private static Row rowOf(CharSequence text) {
        List<Forecast> elements = new ArrayList<>();
        Matcher found = ELEMENT.matcher(text);
        while (found.find()) {
            elements.add(new Forecast(found.group(1), Integer.parseInt(found.group(2)),
                    found.group(3) == null || Boolean.parseBoolean(found.group(3))));
        }
        Matcher beside = BESIDE.matcher(text);
        return new Row(beside.find() ? Integer.parseInt(beside.group(1)) : 0, elements);
    }

    /**
     * Every row composed, run as an example answering what {@code answer} says of it.
     *
     * @param held  how many of what is counted the row holds, which the line is drawn at
     * @param every what each row composed keeps to besides
     * @return the counts the rows hold
     */
    private static Set<Long> rowsComposedHold(String source, ToIntFunction<Row> answer,
                                              ToLongFunction<Row> held, Consumer<Row> every) {
        Compilation compilation = measured(source);
        String rows = GeneratedRows.of(compilation, "probe", null,
                SourceRendering.namedByIdentity(compilation.texts())).text();
        StringBuilder examples = new StringBuilder("\nexample f\n");
        StringBuilder text = new StringBuilder();
        Set<Long> counts = new HashSet<>();
        for (String line : rows.split("\n")) {
            if (line.startsWith("//")) {
                continue;
            }
            if (line.startsWith("    |")) {
                text = new StringBuilder();
            }
            text.append(line).append('\n');
            if (!line.contains("<?>")) {
                continue;
            }
            Row row = rowOf(text);
            counts.add(held.applyAsLong(row));
            every.accept(row);
            examples.append(text.toString().replace("<?>", String.valueOf(answer.applyAsInt(row))));
        }
        assertFalse(counts.isEmpty(), () -> "rows composed: " + rows);
        measured(source + examples);
        return counts;
    }

    private static Set<Long> rowsComposedHold(String source, ToIntFunction<Row> answer,
                                              ToLongFunction<Row> held) {
        return rowsComposedHold(source, answer, held, _ -> { });
    }

    private static boolean aboveHalf(Row row, Forecast each) {
        return each.amount() * 2 > row.total();
    }

    private static long elementsAboveHalf(Row row) {
        return row.countOf(each -> aboveHalf(row, each));
    }

    private static long currenciesAboveHalf(Row row) {
        return row.elements().stream().filter(each -> aboveHalf(row, each))
                .map(Forecast::currency).distinct().count();
    }

    private static final String ONE_ABOVE_HALF = source(PLAIN, FS,
            "if " + listCount(HALF) + " == 1 then 1 else 0");

    private static final String CURRENCIES_ABOVE_HALF = source(PLAIN, FS,
            "if Set.size(Set.fromList(List.map(.currency, List.filter(f -> " + HALF
                    + ", fs)))) == 1 then 1 else 0");

    /** Every point of the line that a value can stand at has a row. */
    private static void everyPointHasARow(String source) {
        List<JsonNode> lines = countLines(measured(source));
        assertFalse(lines.isEmpty());
        for (JsonNode line : lines) {
            for (JsonNode item : line.path("items")) {
                assertTrue(item.has("notOwed") || item.path("knownWritable").asBoolean(),
                        item::toString);
            }
        }
    }

    @Test
    void everyPointOfTheLineOnTheElementsMeetingItHasARow() {
        everyPointHasARow(ONE_ABOVE_HALF);
    }

    @Test
    void everyPointOfTheLineOnTheCurrenciesOfThoseMeetingItHasARow() {
        everyPointHasARow(CURRENCIES_ABOVE_HALF);
    }

    /**
     * The line is drawn at one, at nought, at two and past two, and a row is composed holding
     * each. Past two every element is above half of a total below nought, which an element read
     * against a total of itself alone is not.
     */
    @Test
    void theRowsComposedHoldTheCountOfElementsTheirPointsAsk() {
        Set<Long> counts = rowsComposedHold(ONE_ABOVE_HALF,
                row -> elementsAboveHalf(row) == 1 ? 1 : 0, row -> elementsAboveHalf(row));
        assertTrue(counts.containsAll(List.of(0L, 1L, 2L)), counts::toString);
        assertTrue(counts.stream().anyMatch(count -> count > 2), counts::toString);
    }

    @Test
    void theRowsComposedHoldTheCountOfCurrenciesTheirPointsAsk() {
        Set<Long> counts = rowsComposedHold(CURRENCIES_ABOVE_HALF,
                row -> currenciesAboveHalf(row) == 1 ? 1 : 0,
                AStatementReadingTheWholeContainerIsComposedAgainstItsTotalTest::currenciesAboveHalf);
        assertTrue(counts.containsAll(List.of(0L, 1L, 2L)), counts::toString);
        assertTrue(counts.stream().anyMatch(count -> count > 2), counts::toString);
    }

    /** Where no element meets the statement in a container of itself alone, a row holding one is
     *  composed all the same: it is the total of the container that the element is above. */
    @Test
    void anElementAboveTheRestByTenIsComposedThoughNoneIsAboveItselfByTen() {
        String source = source(PLAIN, FS, "if " + listCount(
                "f.amount > List.sum(List.map(.amount, fs)) + 10") + " == 1 then 1 else 0");
        Set<Long> counts = rowsComposedHold(source, row -> row.countOf(
                each -> each.amount() > row.total() + 10) == 1 ? 1 : 0,
                row -> row.countOf(each -> each.amount() > row.total() + 10));
        assertTrue(counts.contains(1L), counts::toString);
    }

    /**
     * No row composed holds a value its type does not leave an element, however far that is from
     * the values near nought a count of one is first met at: every element is between a hundred
     * and a hundred and two. (That the values are chosen within what the type leaves is what
     * {@link #theElementsOfOneKindAreNotAllOneValue} asks for; this asks that no row goes past
     * it.)
     */
    @Test
    void noRowComposedHoldsAValueTheTypeDoesNotLeaveAnElement() {
        String source = source("data Forecast = { currency: String, amount: Int }"
                + " invariant amount >= 100 invariant amount <= 102\n", FS,
                "if " + listCount(HALF) + " == 1 then 1 else 0");
        Set<Long> counts = rowsComposedHold(source, row -> elementsAboveHalf(row) == 1 ? 1 : 0,
                row -> elementsAboveHalf(row),
                row -> row.elements().forEach(each -> assertTrue(
                        each.amount() >= 100 && each.amount() <= 102,
                        () -> "an element of the type: " + each)));
        assertTrue(counts.contains(1L), counts::toString);
        assertTrue(counts.contains(0L), counts::toString);
    }

    /** A threshold far from the sizes of the container is reached: the values follow the
     *  statement and not the container's size. */
    @Test
    void anElementAboveTheRestByAThousandIsComposed() {
        String source = source(PLAIN, FS, "if " + listCount(
                "f.amount > List.sum(List.map(.amount, fs)) + 1000") + " == 1 then 1 else 0");
        Set<Long> counts = rowsComposedHold(source, row -> row.countOf(
                each -> each.amount() > row.total() + 1000) == 1 ? 1 : 0,
                row -> row.countOf(each -> each.amount() > row.total() + 1000));
        assertTrue(counts.contains(1L), counts::toString);
    }

    /**
     * What an element's other positions say changes what it answers, and a row is composed for
     * each: an element above half of the total that is not active does not meet the statement,
     * and one that is, does.
     */
    @Test
    void aTruthOfTheElementIsChosenBothWays() {
        String source = source("data Forecast = { currency: String, amount: Int, active: Bool }\n",
                FS, "if " + listCount(HALF + " && f.active") + " == 1 then 1 else 0");
        boolean[] aboveHalfButInactive = {false};
        boolean[] aboveHalfAndActive = {false};
        Set<Long> counts = rowsComposedHold(source,
                row -> row.countOf(each -> aboveHalf(row, each) && each.active()) == 1 ? 1 : 0,
                row -> row.countOf(each -> aboveHalf(row, each) && each.active()),
                row -> {
                    aboveHalfButInactive[0] |= row.elements().stream()
                            .anyMatch(each -> aboveHalf(row, each) && !each.active());
                    aboveHalfAndActive[0] |= row.elements().stream()
                            .anyMatch(each -> aboveHalf(row, each) && each.active());
                });
        assertTrue(counts.containsAll(List.of(0L, 1L)), counts::toString);
        assertTrue(aboveHalfButInactive[0], "an element above half that is not active");
        assertTrue(aboveHalfAndActive[0], "an element above half that is active");
    }

    /**
     * The elements of one way of answering are not all one value. Between nought and two, with
     * the total at three, exactly two below two are nought and one, and the third is two.
     */
    @Test
    void theElementsOfOneKindAreNotAllOneValue() {
        String source = source("data Forecast = { currency: String, amount: Int }"
                + " invariant amount >= 0 invariant amount <= 2\n", FS,
                "if " + listCount("f.amount < 2 && List.sum(List.map(.amount, fs)) == 3")
                        + " == 2 then 1 else 0");
        Set<Long> counts = rowsComposedHold(source,
                row -> row.total() == 3 && row.countOf(each -> each.amount() < 2) == 2 ? 1 : 0,
                row -> row.total() == 3 ? row.countOf(each -> each.amount() < 2) : 0);
        assertTrue(counts.contains(2L), counts::toString);
    }

    /**
     * How many the container holds is asked as well. Three of nine: a container of the least
     * size that holds three above half of its total is a smaller one, and the containers offered
     * for a count are few, so the ones of the size asked are reached only by walking the sizes
     * that are.
     */
    @Test
    void theSizeOfTheContainerIsAskedAsWell() {
        String source = source(PLAIN, FS, "if List.length(fs) == 9 && "
                + listCount(HALF) + " == 3 then 1 else 0");
        Set<Long> counts = rowsComposedHold(source,
                row -> row.elements().size() == 9 && elementsAboveHalf(row) == 3 ? 1 : 0,
                row -> elementsAboveHalf(row) == 3 && row.elements().size() == 9 ? 3 : 0);
        assertTrue(counts.contains(3L), counts::toString);
    }

    /** A number outside the container is read at the one value the row is fixed at, which is not
     *  nought here: the rows keep to above three. */
    @Test
    void aNumberBesideTheContainerIsReadAtTheValueTheRowHolds() {
        String source = source(PLAIN, K_AND_FS, "if k > 3 && " + listCount(
                "f.amount * 2 > List.sum(List.map(.amount, fs)) + k") + " == 1 then 1 else 0");
        Set<Long> counts = rowsComposedHold(source, row -> row.k() > 3 && row.countOf(
                each -> each.amount() * 2 > row.total() + row.k()) == 1 ? 1 : 0,
                row -> row.countOf(each -> each.amount() * 2 > row.total() + row.k()));
        assertTrue(counts.contains(1L), counts::toString);
    }

    /**
     * A relation that reads nothing of the container once the number beside it is fixed stands
     * the same way for every element, so it is a truth of the row: here the same number above
     * three, asked in the statement and outside it, and the rows composed are those of the
     * statement without it. (A way of standing the relation never has is dropped before the
     * sharings are looked at, which saves figures and changes no row.)
     */
    @Test
    void aRelationOfNothingInTheContainerIsATruthOfTheRow() {
        String source = source(PLAIN, K_AND_FS, "if k > 3 && " + listCount("k > 3 && " + HALF)
                + " == 1 then 1 else 0");
        Set<Long> counts = rowsComposedHold(source,
                row -> row.k() > 3 && row.k() > 3 && elementsAboveHalf(row) == 1 ? 1 : 0,
                row -> row.k() > 3 ? elementsAboveHalf(row) : 0);
        assertTrue(counts.contains(1L), counts::toString);
    }

    /** Two counts asked together are composed together. */
    @Test
    void twoCountsAskedTogetherAreComposedTogether() {
        String source = source(PLAIN, FS, "if " + listCount(HALF)
                + " == 1 && " + listCount("f.amount < 0") + " == 1 then 1 else 0");
        Set<Long> counts = rowsComposedHold(source,
                row -> elementsAboveHalf(row) == 1 && row.countOf(each -> each.amount() < 0) == 1
                        ? 1 : 0,
                row -> row.countOf(each -> each.amount() < 0));
        assertTrue(counts.containsAll(List.of(0L, 1L, 2L)), counts::toString);
    }

    /**
     * A statement that asks of its own value the place whose different values are counted is
     * left to the composition that does not read the total, and said to be: the values that place
     * is offered are chosen apart from what the statement reads, which here it reads.
     */
    @Test
    void aStatementThatReadsThePlaceCountedIsLeftToTheCompositionThatDoesNotReadTheTotal() {
        String source = source("data Forecast = { currency: String, amount: Int, active: Bool }\n",
                FS, "if Set.size(Set.fromList(List.map(.active, "
                        + "List.filter(f -> f.active && " + HALF + ", fs)))) == 1 then 1 else 0");
        Compilation compilation = measured(source);
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        assertLeftToTheCompositionThatDoesNotReadTheTotal(report);
    }

    /**
     * A statement that asks of its own value a position outside the container is left to the
     * composition that does not read the total, and said to be: the observation the elements are
     * read in holds the container and the numbers beside it, and there is nothing in it to read
     * that position from.
     */
    @Test
    void aStatementThatReadsAPositionOutsideTheContainerIsLeftToTheCompositionThatDoesNotReadTheTotal() {
        String source = source(PLAIN, new Parameters("enabled: Bool, fs: List<Forecast>",
                "enabled, fs"), "if " + listCount("enabled && " + HALF) + " == 1 then 1 else 0");
        Compilation compilation = measured(source);
        String report = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        assertLeftToTheCompositionThatDoesNotReadTheTotal(report);
    }

    /** What the other composition says of an element it cannot choose the values of, and what this
     *  one says where it stops: the first is the one a statement it does not take is left to. */
    private static void assertLeftToTheCompositionThatDoesNotReadTheTotal(String report) {
        assertTrue(report.contains("has a part whose values are neither one of so many nor"
                + " numbers the statements part"), report);
        assertFalse(report.contains("answers turns on the total of"), report);
    }

    /**
     * A count more elements than a container is composed with is not shown to have no row: the
     * point is said to be one a figure stopped, and never one no value can stand at.
     */
    @Test
    void aCountPastTheElementsAContainerIsComposedWithIsNotShownToBeOutOfReach() {
        String source = source(PLAIN, FS, "if " + listCount(HALF)
                + " == 20 then 1 else 0");
        List<JsonNode> lines = countLines(measured(source));
        assertFalse(lines.isEmpty());
        boolean unwritable = false;
        for (JsonNode line : lines) {
            for (JsonNode item : line.path("items")) {
                if ("20".equals(item.path("against").asString())) {
                    unwritable |= !item.path("knownWritable").asBoolean();
                    assertFalse(item.has("notOwed"), item::toString);
                }
            }
        }
        assertTrue(unwritable, "the point at twenty has no row composed");
    }
}
