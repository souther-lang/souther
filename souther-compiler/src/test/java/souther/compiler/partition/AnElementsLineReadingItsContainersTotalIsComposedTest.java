package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;
import java.util.function.ToIntBiFunction;
import java.util.function.ToIntFunction;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The line of an element's statement that reads the total of the container the element is in has
 * a row at each of its points, composed as one container: the element at its value and the others
 * coming to what the total leaves.
 *
 * <p>Each row is run as an example answering what the language computes of it, and stands at the
 * point it was composed for: some element of it is at that point of the line, read against the
 * total of the container it is in. A container of the element alone stands at one point of
 * {@code f.amount > total - 10} and at no other, so the rows there hold more than one element.
 */
class AnElementsLineReadingItsContainersTotalIsComposedTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String DATA = "data Forecast = { currency: String, amount: Int }\n";

    private static final Pattern ELEMENT =
            Pattern.compile("currency = \"([^\"]*)\", amount = (-?\\d+)");

    private static final Pattern FILLS =
            Pattern.compile("fills (ON|OFF|IN|OUT) point of (comparison@\\S+)");

    /** An element of a row composed. */
    private record Forecast(String currency, int amount) {}

    /** A row composed, and the points of the comparisons it is said to fill. */
    private record Row(List<Forecast> elements, Map<String, Set<String>> fills, String text) {

        int total() {
            return elements.stream().mapToInt(Forecast::amount).sum();
        }
    }

    /** A point of a line: a number the line stands at, or the side of the line it is past. */
    private record Point(BigDecimal at, String side) {}

    private static final String HALF = "f.amount * 2 > List.sum(List.map(.amount, fs))";

    private static final String THIRD = "f.amount * 3 > List.sum(List.map(.amount, fs))";

    private static final String TEN_BELOW = "f.amount > List.sum(List.map(.amount, fs)) - 10";

    private static String counted(String statement) {
        return "if List.length(List.filter(f -> " + statement + ", fs)) == 1 then 1 else 0";
    }

    private static String currencies(String statement) {
        return "if Set.size(Set.fromList(List.map(.currency, List.filter(f -> " + statement
                + ", fs)))) == 1 then 1 else 0";
    }

    private static String source(String parameters, String names, String body) {
        return "module probe\n\n" + DATA + "\nbehavior f : (" + parameters + ") -> Int\nlet f ("
                + names + ") = " + body + "\n";
    }

    private static String ofFs(String body) {
        return source("fs: List<Forecast>", "fs", body);
    }

    /** {@code body} over the list {@code fs} of a record whose rule is {@code rule}. */
    private static String inABox(String rule, String body) {
        return "module probe\n\n" + DATA + "data Box = { fs: List<Forecast> } invariant " + rule
                + "\n\nbehavior f : (b: Box) -> Int\nlet f (b) = "
                + body.replaceAll("\\bfs\\b", "b.fs") + "\n";
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

    /** The points of the line {@code axis}, by the name a row says it fills each as. */
    private static Map<String, Point> pointsOf(Compilation compilation, String axis) {
        JsonNode report = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        Map<String, Point> out = new LinkedHashMap<>();
        List<BigDecimal> at = new ArrayList<>();
        for (JsonNode behavior : report.at("/modules/0/behaviors")) {
            for (JsonNode line : behavior.at("/partition/boundaries")) {
                if (!line.path("axis").asString().equals("f/" + axis)) {
                    continue;
                }
                for (JsonNode item : line.path("items")) {
                    assertTrue(item.path("knownWritable").asBoolean(), item::toString);
                    String name = item.path("point").asString().toUpperCase(Locale.ROOT);
                    if ("=".equals(item.path("relation").asString())) {
                        BigDecimal number = new BigDecimal(item.path("against").asString());
                        at.add(number);
                        out.put(name, new Point(number, null));
                    } else {
                        out.put(name, new Point(null,
                                item.path("location").path("side").asString()));
                    }
                }
            }
        }
        assertEquals(Set.of("ON", "OFF", "IN", "OUT"), out.keySet(), () -> axis + ": " + out);
        // A side of the line is past every number the line is drawn at on that side.
        BigDecimal least = at.stream().min(BigDecimal::compareTo).orElseThrow();
        BigDecimal most = at.stream().max(BigDecimal::compareTo).orElseThrow();
        out.replaceAll((name, point) -> point.at() != null ? point
                : new Point("below".equals(point.side()) ? least : most, point.side()));
        return out;
    }

    private static boolean stands(int value, Point point) {
        int against = point.at().compareTo(BigDecimal.valueOf(value));
        return switch (point.side() == null ? "at" : point.side()) {
            case "below" -> against > 0;
            case "above" -> against < 0;
            default -> against == 0;
        };
    }

    private static List<Row> rowsOf(Compilation compilation) {
        String rows = GeneratedRows.of(compilation, "probe", null,
                SourceRendering.namedByIdentity(compilation.texts())).text();
        List<Row> out = new ArrayList<>();
        Map<String, Set<String>> fills = new LinkedHashMap<>();
        StringBuilder text = new StringBuilder();
        for (String line : rows.split("\n")) {
            if (line.startsWith("//")) {
                Matcher fill = FILLS.matcher(line);
                if (fill.find()) {
                    fills.computeIfAbsent(fill.group(2), _ -> new HashSet<>()).add(fill.group(1));
                }
                continue;
            }
            if (line.startsWith("    |")) {
                text = new StringBuilder();
            }
            text.append(line).append('\n');
            if (!line.contains("<?>")) {
                continue;
            }
            List<Forecast> elements = new ArrayList<>();
            Matcher found = ELEMENT.matcher(text);
            while (found.find()) {
                elements.add(new Forecast(found.group(1), Integer.parseInt(found.group(2))));
            }
            out.add(new Row(List.copyOf(elements), Map.copyOf(fills), text.toString()));
            fills = new LinkedHashMap<>();
        }
        assertFalse(out.isEmpty(), rows);
        return out;
    }

    /**
     * Every point of the element's line {@code axis} has a row, the row is run as an example of
     * what {@code answer} says of it, and some element of it stands at the point.
     *
     * @param statement the element's statement, whose comparison the rows say they fill
     * @param line      the element's line, of the element and of the row it is in
     */
    private static void everyPointHasARowStandingAtIt(String source, String statement,
                                                      String axis,
                                                      ToIntBiFunction<Row, Forecast> line,
                                                      ToIntFunction<Row> answer) {
        Compilation compilation = measured(source);
        Map<String, Point> points = pointsOf(compilation, axis);
        String comparison = comparisonOf(source, statement);
        Set<String> filled = new HashSet<>();
        StringBuilder examples = new StringBuilder("\nexample f\n");
        for (Row row : rowsOf(compilation)) {
            for (String name : row.fills().getOrDefault(comparison, Set.of())) {
                Point point = points.get(name);
                assertNotNull(point, name);
                assertTrue(row.elements().stream()
                                .anyMatch(each -> stands(line.applyAsInt(row, each), point)),
                        () -> name + " " + point + " in " + row.text());
                filled.add(name);
            }
            examples.append(row.text().replace("<?>", String.valueOf(answer.applyAsInt(row))));
        }
        assertEquals(points.keySet(), filled, "every point of " + axis + " has a row");
        measured(source + examples);
    }

    /** The comparison the statement is, as a row names it: the line and column of its {@code >}. */
    private static String comparisonOf(String source, String statement) {
        String[] lines = source.split("\n", -1);
        for (int i = 0; i < lines.length; i++) {
            int at = lines[i].indexOf(statement);
            if (at >= 0) {
                return "comparison@0:" + (i + 1) + ":" + (at + statement.indexOf(" > ") + 2);
            }
        }
        throw new AssertionError(statement + " in " + source);
    }

    private static long countOf(Row row, Predicate<Forecast> meets) {
        return row.elements().stream().filter(meets).count();
    }

    @Test
    void everyPointOfTheLineOfAnElementAboveHalfOfItsContainerHasARow() {
        everyPointHasARowStandingAtIt(ofFs(counted(HALF)), HALF,
                "List.sum(fs[*].amount) - 2 * fs[*].amount",
                (row, each) -> row.total() - 2 * each.amount(),
                row -> countOf(row, each -> each.amount() * 2 > row.total()) == 1 ? 1 : 0);
    }

    @Test
    void everyPointOfTheLineOfAnElementAboveAThirdOfItsContainerHasARow() {
        everyPointHasARowStandingAtIt(ofFs(counted(THIRD)), THIRD,
                "List.sum(fs[*].amount) - 3 * fs[*].amount",
                (row, each) -> row.total() - 3 * each.amount(),
                row -> countOf(row, each -> each.amount() * 3 > row.total()) == 1 ? 1 : 0);
    }

    /**
     * What the others come to is the line here: a container of the element alone comes to the
     * element and stands at ten, so every other point is a row holding more than one element.
     */
    @Test
    void everyPointOfTheLineOfAnElementAboveItsContainerLessTenHasARow() {
        everyPointHasARowStandingAtIt(ofFs(counted(TEN_BELOW)), TEN_BELOW,
                "List.sum(fs[*].amount) - fs[*].amount",
                (row, each) -> row.total() - each.amount(),
                row -> countOf(row, each -> each.amount() > row.total() - 10) == 1 ? 1 : 0);
    }

    @Test
    void everyPointOfTheLineOfTheCurrenciesOfElementsAboveHalfHasARow() {
        everyPointHasARowStandingAtIt(ofFs(currencies(HALF)), HALF,
                "List.sum(fs[*].amount) - 2 * fs[*].amount",
                (row, each) -> row.total() - 2 * each.amount(),
                row -> row.elements().stream().filter(each -> each.amount() * 2 > row.total())
                        .map(Forecast::currency).distinct().count() == 1 ? 1 : 0);
    }

    /** The two lists a row of two parameters holds, in the order they are written. */
    private static final Pattern BETWEEN_TWO_LISTS = Pattern.compile("\\]\\s*,\\s*\\[");

    /**
     * An element read against the total of another container is no share of it: the element and
     * the total are written at two locations, and the line has a row at each point as it does
     * where nothing groups them — some element of the first container standing at the point
     * against what the second comes to.
     */
    @Test
    void anElementReadAgainstAnotherContainersTotalIsComposedApartFromIt() {
        String statement = "f.amount * 2 > List.sum(List.map(.amount, gs))";
        String source = source("fs: List<Forecast>, gs: List<Forecast>", "fs, gs",
                counted(statement));
        Compilation compilation = measured(source);
        Map<String, Point> points = pointsOf(compilation,
                "-List.sum(gs[*].amount) + 2 * fs[*].amount");
        String comparison = comparisonOf(source, statement);
        Set<String> filled = new HashSet<>();
        for (Row row : rowsOf(compilation)) {
            String[] lists = BETWEEN_TWO_LISTS.split(row.text(), 2);
            assertEquals(2, lists.length, row.text());
            List<Forecast> fs = elementsIn(lists[0]);
            int gs = elementsIn(lists[1]).stream().mapToInt(Forecast::amount).sum();
            for (String name : row.fills().getOrDefault(comparison, Set.of())) {
                Point point = points.get(name);
                assertNotNull(point, name);
                assertTrue(fs.stream().anyMatch(each -> stands(2 * each.amount() - gs, point)),
                        () -> name + " " + point + " in " + row.text());
                filled.add(name);
            }
        }
        assertEquals(points.keySet(), filled);
    }

    private static List<Forecast> elementsIn(String text) {
        List<Forecast> out = new ArrayList<>();
        Matcher found = ELEMENT.matcher(text);
        while (found.find()) {
            out.add(new Forecast(found.group(1), Integer.parseInt(found.group(2))));
        }
        return out;
    }

    /**
     * Every number of a container as a whole an element is read against is fixed before the
     * element is chosen, whatever number it is: how many it holds, what a form of its elements'
     * numbers comes to, what another of their fields comes to, two totals at once, what a list of
     * numbers comes to — and a total a condition on the way asks rather than the point. Every
     * point of every line of each has a row or is owed none.
     *
     * <p>And fixed where the rules leave it. A record holding its total to at least a hundred, or
     * its length to at least ten, leaves no row at a number below, so a number tried there is one
     * no input has; and a total of another container is one number of the row, fixed beside the
     * elements as an input is.
     */
    @Test
    void everyNumberOfTheWholeAnElementIsReadAgainstIsFixedBeforeTheElementIsChosen() {
        String qty = "data Forecast = { amount: Int, qty: Int }\n";
        Map<String, String> models = new LinkedHashMap<>();
        models.put("how many it holds", ofFs(counted("f.amount > List.length(fs)")));
        models.put("a form of the numbers",
                ofFs(counted("f.amount * 2 > List.sum(List.map(g -> g.amount + 1, fs))")));
        models.put("a total on the way", ofFs("if List.sum(List.map(.amount, fs)) > 10 then ("
                + counted("f.amount > 3") + ") else 0"));
        models.put("another field", "module probe\n\n" + qty + "\nbehavior f : (fs: List<Forecast>)"
                + " -> Int\nlet f (fs) = " + counted("f.amount > List.sum(List.map(.qty, fs))")
                + "\n");
        models.put("two totals", "module probe\n\n" + qty + "\nbehavior f : (fs: List<Forecast>)"
                + " -> Int\nlet f (fs) = " + counted("f.amount * 2 > List.sum(List.map(.amount,"
                + " fs)) + List.sum(List.map(.qty, fs))") + "\n");
        models.put("a list of numbers", "module probe\n\nbehavior f : (xs: List<Int>) -> Int\n"
                + "let f (xs) = if List.length(List.filter(x -> x * 2 > List.sum(xs), xs)) == 1"
                + " then 1 else 0\n");
        models.put("a total its record holds", inABox("List.sum(List.map(.amount, fs)) >= 100",
                counted(HALF)));
        models.put("a length its record holds", inABox("List.length(fs) >= 10",
                counted("f.amount > List.length(fs)")));
        models.put("another container's total", source("fs: List<Forecast>, gs: List<Forecast>",
                "fs, gs", counted("f.amount * 2 > List.sum(List.map(.amount, gs))")));
        models.forEach((name, source) -> {
            Compilation compilation = measured(source);
            JsonNode report = JSON.readTree(AdequacyReport.of(compilation)
                    .json(SourceRendering.namedByIdentity(compilation.texts())));
            int items = 0;
            for (JsonNode behavior : report.at("/modules/0/behaviors")) {
                for (JsonNode line : behavior.at("/partition/boundaries")) {
                    for (JsonNode item : line.path("items")) {
                        items++;
                        assertTrue(item.has("notOwed") || item.path("knownWritable").asBoolean(),
                                () -> name + ": " + line.path("axis").asString() + " " + item);
                    }
                }
            }
            assertTrue(items > 0, name);
        });
    }
}
