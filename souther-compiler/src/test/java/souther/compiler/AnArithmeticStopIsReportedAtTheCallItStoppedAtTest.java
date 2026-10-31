package souther.compiler;

import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeMap;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A comparison whose arithmetic stopped is reported at the call the arithmetic stopped at, place
 * by place, in the document and in the text a person reads.
 *
 * <p>The date a weekday is counted of is a value some operation answered in the first model — one
 * a search found, one a month was added to — and the word for the rule changes with it. The call
 * the reading stopped at does not: it is the remainder in {@code weekday}, and not the difference
 * of days inside it. The second model has two remainders over two positions, and each position
 * is sent to the remainder it went through. A clause of an {@code ensures} is sent to its call as
 * a comparison in a body is.
 *
 * <p>Compiled once each, because what is asked of every behavior is its own.
 */
class AnArithmeticStopIsReportedAtTheCallItStoppedAtTest {

    private static final String WEEKDAYS = """
            module probe.stop

            data PaymentCalendar = { holidays: Set<Date>, aSunday: Date }
            data Open
            data Closed

            let weekday (calendar: PaymentCalendar, d: Date): Int =
                Int.floorMod(Date.daysBetween(calendar.aSunday, d), 7)

            let isBusinessDay (calendar: PaymentCalendar, d: Date): Bool =
                weekday(calendar, d) >= 1 && weekday(calendar, d) <= 5

            behavior found : (c: PaymentCalendar, from: Date, xs: List<Date>) -> Bool
            let found (c, from, xs) = isBusinessDay(c,
                Option.withDefault(from, List.find(d -> d == from, xs)))

            behavior monthAdded : (c: PaymentCalendar, from: Date) -> Bool
            let monthAdded (c, from) = isBusinessDay(c, Date.addMonths(1, from))

            behavior daysAdded : (c: PaymentCalendar, from: Date) -> Bool
            let daysAdded (c, from) = isBusinessDay(c, Date.addDays(3, from))

            behavior promised : (c: PaymentCalendar, from: Date, xs: List<Date>) -> Open | Closed
                ensures Open -> weekday(c, Option.withDefault(from,
                    List.find(d -> d == from, xs))) >= 1
            let promised (c, from, xs) = Open
            """;

    private static final String TWO_REMAINDERS = """
            module probe.pairs

            let first (d: Date, xs: List<Date>): Date =
                Option.withDefault(d, List.find(x -> x == d, xs))

            let weekOf (s: Date, d: Date): Int =
                Int.floorMod(Date.daysBetween(s, first(d, [ d ])), 7)

            let fiveDaysOf (s: Date, d: Date): Int =
                Int.floorMod(Date.daysBetween(s, first(d, [ d ])), 5)

            behavior f : (s: Date, a: Date, b: Date) -> Bool
            let f (s, a, b) = List.any(v -> v >= 1, [ weekOf(s, a), fiveDaysOf(s, b) ])
            """;

    /** The same stop in a rule written on a type, in one part and in two. */
    private static final String ONE_PART = """
            module probe.inv

            data Slot = { at: Date, xs: List<Date> }
                invariant ok = Int.floorMod(Date.daysBetween(at,
                    Option.withDefault(at, List.find(d -> d == at, xs))), 7) >= 1

            data Done

            behavior f : (s: Slot) -> Done
            let f (s) = Done
            """;

    private static final String TWO_PARTS = """
            module probe.inv

            data Slot = { at: Date, xs: List<Date> }
                invariant ok = Int.floorMod(Date.daysBetween(at,
                    Option.withDefault(at, List.find(d -> d == at, xs))), 7) >= 1
                    && Int.floorMod(Date.daysBetween(at,
                    Option.withDefault(at, List.find(d -> d == at, xs))), 5) >= 1

            data Done

            behavior f : (s: Slot) -> Done
            let f (s) = Done
            """;

    private static final String DERIVED = "rule_about_a_derived_value";

    /** What one compilation said, as the document and as the text. */
    private record Said(JsonNode document, String text) {}

    private static Said weekdays;
    private static Said pairs;
    private static Said onePart;
    private static Said twoParts;

    @BeforeAll
    static void compileTheModelsOnce() {
        weekdays = said(WEEKDAYS);
        pairs = said(TWO_REMAINDERS);
        onePart = said(ONE_PART);
        twoParts = said(TWO_PARTS);
    }

    private static Said said(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList());
        AdequacyReport report = AdequacyReport.of(compilation);
        SourceRendering rendering = SourceRendering.namedByIdentity(compilation.texts());
        return new Said(JsonMapper.builder().build().readTree(report.json(rendering)),
                report.human(rendering));
    }

    /** Where the one {@code needle} in {@code source} is, as a report spells a place. */
    private static String placeOf(String source, String needle) {
        return placeOf(source, "", needle);
    }

    /**
     * Where {@code needle} is, found by what is written just before it: the place a call is
     * written at when the same call is written more than once.
     */
    private static String placeOf(String source, String before, String needle) {
        int offset = source.indexOf(before + needle);
        assertEquals(source.lastIndexOf(before + needle), offset,
                before + needle + " is written once");
        offset += before.length();
        int line = (int) source.substring(0, offset).chars().filter(c -> c == '\n').count() + 1;
        return line + ":" + (offset - source.lastIndexOf('\n', offset));
    }

    /**
     * The places of the rules of {@code behavior} that were not read for the derived-value word,
     * each with the places in the source it is sent to.
     */
    private static Map<String, Set<String>> sentTo(Said said, String behavior) {
        Map<String, Set<String>> out = new TreeMap<>();
        for (JsonNode each : said.document().findParents("partition")) {
            if (!behavior.equals(each.get("name").asString())) {
                continue;
            }
            for (JsonNode entry : each.get("partition").get("notRead")) {
                if (!DERIVED.equals(entry.get("reason").asString())) {
                    continue;
                }
                Set<String> sites = out.computeIfAbsent(entry.get("position").asString(),
                        _ -> new TreeSet<>());
                JsonNode at = entry.get("sentTo");
                assertFalse(at == null, () -> "every rule of this word is sent to a call: " + entry);
                sites.add(at.get("line").asInt() + ":" + at.get("column").asInt());
            }
        }
        return out;
    }

    private static void assertEveryPlaceIsSentTo(Said said, String behavior, String call) {
        Map<String, Set<String>> sent = sentTo(said, behavior);
        assertFalse(sent.isEmpty(), "the model stops the reading, or this checks nothing");
        sent.forEach((place, sites) -> assertEquals(Set.of(call), sites,
                () -> "`" + place + "` is sent to the remainder and to nothing else"));
    }

    @Test
    void aDateASearchFoundIsSentToTheRemainderAndNotToTheDaysInIt() {
        assertEveryPlaceIsSentTo(weekdays, "found",
                placeOf(WEEKDAYS, "Int.floorMod(Date.daysBetween(calendar.aSunday, d), 7)"));
    }

    @Test
    void aDateAMonthWasAddedToIsSentToTheSameCall() {
        assertEveryPlaceIsSentTo(weekdays, "monthAdded",
                placeOf(WEEKDAYS, "Int.floorMod(Date.daysBetween(calendar.aSunday, d), 7)"));
    }

    @Test
    void aClauseOfAnEnsuresIsSentToItsCallAsAComparisonInABodyIs() {
        assertEveryPlaceIsSentTo(weekdays, "promised",
                placeOf(WEEKDAYS, "Int.floorMod(Date.daysBetween(calendar.aSunday, d), 7)"));
    }

    /**
     * Where the date is a position and the weekday is read to the end, nothing stopped the
     * arithmetic, and no rule is sent to a call.
     */
    @Test
    void aDateThatIsAPositionStopsNothingAndIsSentNowhere() {
        assertEquals(Map.of(), sentTo(weekdays, "daysAdded"));
    }

    /**
     * Two remainders over two positions, put together as the applications of one closure: each
     * position is sent to the remainder it went through, and the one both went through to both.
     */
    @Test
    void eachPlaceIsSentToTheRemainderItWentThroughAndToNoOther() {
        String week = placeOf(TWO_REMAINDERS,
                "Int.floorMod(Date.daysBetween(s, first(d, [ d ])), 7)");
        String five = placeOf(TWO_REMAINDERS,
                "Int.floorMod(Date.daysBetween(s, first(d, [ d ])), 5)");

        assertEquals(Map.of("s", Set.of(week, five), "a", Set.of(week), "b", Set.of(five)),
                sentTo(pairs, "f"));
    }

    /**
     * Every place the document sends a reader about a rule of a type whose arithmetic stopped: the
     * rules not read and the questions left open. Each must be sent somewhere, and the places are
     * returned as a set since the rule is one and the position is another.
     */
    private static Set<String> sentToAboutTheRuleOfAType(Said said) {
        Set<String> out = new TreeSet<>();
        List<JsonNode> entries = new ArrayList<>();
        for (JsonNode behavior : said.document().findParents("partition")) {
            behavior.get("partition").get("notRead").forEach(entries::add);
            for (JsonNode question : behavior.get("partition").get("unanswered")) {
                question.get("stopped").forEach(entries::add);
            }
        }
        for (JsonNode entry : entries) {
            if (!DERIVED.equals(entry.get("reason").asString())) {
                continue;
            }
            JsonNode at = entry.get("sentTo");
            assertFalse(at == null, () -> "a rule of a type is sent to the call too: " + entry);
            out.add(at.get("line").asInt() + ":" + at.get("column").asInt());
        }
        return out;
    }

    @Test
    void aRuleWrittenOnATypeIsSentToTheCallInTheDocumentAndInTheText() {
        String call = placeOf(ONE_PART, "= ", "Int.floorMod(");

        assertEquals(Set.of(call), sentToAboutTheRuleOfAType(onePart));
        List<String> lines = onePart.text().lines().map(String::strip)
                .filter(line -> line.startsWith("· not read: invariant")).toList();
        assertFalse(lines.isEmpty(), "the model stops the reading, or this checks nothing");
        lines.forEach(line -> assertEquals(true, line.endsWith(", at " + call),
                () -> "the text names the call: " + line));
    }

    /**
     * Two parts of one rule stopped at two calls: a reader is sent to both of them, and to the
     * call a part stopped at and never to the rule in place of one.
     */
    @Test
    void eachPartOfARuleIsSentToItsOwnCall() {
        String week = placeOf(TWO_PARTS, "= ", "Int.floorMod(");
        String five = placeOf(TWO_PARTS, "&& ", "Int.floorMod(");

        assertEquals(Set.of(week, five), sentToAboutTheRuleOfAType(twoParts));
    }

    /** And the text a person reads names the same place the document does. */
    @Test
    void theTextNamesThePlaceTheDocumentDoes() {
        String call = placeOf(WEEKDAYS, "Int.floorMod(Date.daysBetween(calendar.aSunday, d), 7)");

        List<String> derived = weekdays.text().lines().map(String::strip)
                .filter(line -> line.startsWith("· not read")
                        && line.contains("it is about a value made from this one"))
                .toList();

        assertFalse(derived.isEmpty(), "the models stop the reading, or this checks nothing");
        derived.forEach(line -> assertEquals(true, line.endsWith(", at " + call),
                () -> "the text names the call: " + line));
    }
}
