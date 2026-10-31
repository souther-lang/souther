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
import java.util.stream.Collectors;

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

            let weekOf (s: Date, d: Date, xs: List<Date>): Int =
                Int.floorMod(Date.daysBetween(s, first(d, xs)), 7)

            let fiveDaysOf (s: Date, d: Date, xs: List<Date>): Int =
                Int.floorMod(Date.daysBetween(s, first(d, xs)), 5)

            behavior f : (s: Date, a: Date, b: Date, xs: List<Date>) -> Bool
            let f (s, a, b, xs) = List.any(v -> v >= 1, [ weekOf(s, a, xs), fiveDaysOf(s, b, xs) ])
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

    /** One position a product stops and a remainder over a search stops, in either order. */
    private static final String REASONS = """
            module probe.reasons

            let viaSearch (n: Int, xs: List<Int>): Int =
                Option.withDefault(n, List.find(x -> x == n, xs))

            let modOf (n: Int, xs: List<Int>): Int = Int.floorMod(viaSearch(n, xs), 7)

            behavior productFirst : (a: Int, xs: List<Int>) -> Bool
            let productFirst (a, xs) = List.any(v -> v >= 1, [ a * a, modOf(a, xs) ])

            behavior remainderFirst : (a: Int, xs: List<Int>) -> Bool
            let remainderFirst (a, xs) = List.any(v -> v >= 1, [ modOf(a, xs), a * a ])
            """;

    /** The same two reasons at one position of a type, in two parts of one rule. */
    private static final String TWO_REASONS_ON_A_TYPE = """
            module probe.inv

            data S = { n: Int, xs: List<Int> }
                invariant ok = Int.floorMod(Option.withDefault(n,
                    List.find(x -> x == n, xs)), 7) >= 1
                    && n * n >= 4

            data Done

            behavior f : (s: S) -> Done
            let f (s) = Done
            """;

    private static final String DERIVED = "rule_about_a_derived_value";

    /** What one compilation said, as the document and as the text. */
    private record Said(JsonNode document, String text) {}

    private static Said weekdays;
    private static Said pairs;
    private static Said onePart;
    private static Said twoParts;
    private static Said reasons;
    private static Said reasonsOnAType;

    @BeforeAll
    static void compileTheModelsOnce() {
        weekdays = said(WEEKDAYS);
        pairs = said(TWO_REMAINDERS);
        onePart = said(ONE_PART);
        twoParts = said(TWO_PARTS);
        reasons = said(REASONS);
        reasonsOnAType = said(TWO_REASONS_ON_A_TYPE);
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

    /** One rule not read at one position: the word it was left with and where it is sent. */
    private record Entry(String position, String reason, String sentTo) {}

    /** Every rule not read in {@code behavior}, whatever the word, and where each is sent. */
    private static List<Entry> notRead(Said said, String behavior) {
        List<Entry> out = new ArrayList<>();
        for (JsonNode each : said.document().findParents("partition")) {
            if (!behavior.equals(each.get("name").asString())) {
                continue;
            }
            for (JsonNode entry : each.get("partition").get("notRead")) {
                JsonNode at = entry.get("sentTo");
                out.add(new Entry(entry.get("position").asString(),
                        entry.get("reason").asString(),
                        at == null ? null : at.get("line").asInt() + ":" + at.get("column").asInt()));
            }
        }
        return out;
    }

    /**
     * Where the date is a position the weekday is read as a remainder, to the end: the reading did
     * not stop, so what is said is the remainder's own word and no rule is sent to a call. Held
     * for the word and not for the absence of one, since a stop under another word would pass a
     * check that asked only about the derived-value word.
     */
    @Test
    void aDateThatIsAPositionIsReadAsARemainderAndIsSentToNoCall() {
        List<Entry> said = notRead(weekdays, "daysAdded");

        assertFalse(said.isEmpty(), "the remainder is reported, or this checks nothing");
        said.forEach(each -> {
            assertEquals("rule_about_a_remainder", each.reason(), () -> "" + each);
            assertEquals(null, each.sentTo(), () -> "" + each);
        });
    }

    /**
     * One position stopped for two reasons by two applications of a closure, in either order: the
     * position is left with the reason of the first, and with the call that stopped it for that
     * reason. The product has no call an author wrote; the remainder has, and the position is not
     * sent to it for the product.
     */
    @Test
    void aPlaceStoppedForTwoReasonsIsSentOnlyToTheCallOfTheOneItIsLeftWith() {
        String call = placeOf(REASONS, "Int.floorMod(viaSearch(n, xs), 7)");

        List<Entry> productFirst = notRead(reasons, "productFirst").stream()
                .filter(each -> each.position().equals("a")).toList();
        List<Entry> remainderFirst = notRead(reasons, "remainderFirst").stream()
                .filter(each -> each.position().equals("a")).toList();

        assertEquals(true, productFirst.contains(new Entry("a", "non_affine_product", null)),
                productFirst.toString());
        assertEquals(List.of(), productFirst.stream()
                .filter(each -> each.reason().equals("non_affine_product")
                        && each.sentTo() != null).toList(),
                "a product is no call, so its place is sent to the rule");
        assertEquals(true, remainderFirst.contains(new Entry("a", DERIVED, call)),
                remainderFirst.toString());
    }

    /**
     * Two remainders over two positions, put together as the applications of one closure: each
     * position is sent to the remainder it went through, and the ones both went through to both.
     * What each is of is found among a list of the input, which no reading writes out.
     */
    @Test
    void eachPlaceIsSentToTheRemainderItWentThroughAndToNoOther() {
        String week = placeOf(TWO_REMAINDERS,
                "Int.floorMod(Date.daysBetween(s, first(d, xs)), 7)");
        String five = placeOf(TWO_REMAINDERS,
                "Int.floorMod(Date.daysBetween(s, first(d, xs)), 5)");

        assertEquals(Map.of("s", Set.of(week, five), "a", Set.of(week), "b", Set.of(five),
                        "xs", Set.of(week, five), "xs[*]", Set.of(week, five)),
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
     * One position of a type stopped for two reasons by two parts of one rule: each reason is sent
     * to its own call, in the rules not read and in both kinds of open question — the remainder
     * to the remainder, and the product, which has no call an author wrote, to the rule.
     */
    @Test
    void eachReasonOnATypeIsSentToItsOwnCallAndToNoOther() {
        String remainder = placeOf(TWO_REASONS_ON_A_TYPE, "= ", "Int.floorMod(");
        List<Entry> entries = new ArrayList<>();
        for (JsonNode behavior : reasonsOnAType.document().findParents("partition")) {
            for (JsonNode entry : behavior.get("partition").get("notRead")) {
                entries.add(entryOf(entry.get("position").asString(), entry));
            }
            for (JsonNode question : behavior.get("partition").get("unanswered")) {
                for (JsonNode stopped : question.get("stopped")) {
                    entries.add(entryOf("", stopped));
                }
            }
        }

        assertEquals(Set.of(DERIVED, "non_affine_product"),
                entries.stream().map(Entry::reason).collect(Collectors.toSet()));
        entries.forEach(each -> assertEquals(
                each.reason().equals(DERIVED) ? remainder : null, each.sentTo(),
                () -> "a reason is sent to the call that stopped it and to no other: " + each));
    }

    private static Entry entryOf(String position, JsonNode entry) {
        JsonNode at = entry.get("sentTo");
        return new Entry(position, entry.get("reason").asString(),
                at == null ? null : at.get("line").asInt() + ":" + at.get("column").asInt());
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
