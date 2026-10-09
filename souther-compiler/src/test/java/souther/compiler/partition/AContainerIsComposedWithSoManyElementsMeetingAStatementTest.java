package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceLayouts;
import souther.compiler.diag.SourceRendering;
import souther.compiler.check.Carrier;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.Endpoint;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.NumericDomain;
import souther.compiler.numeric.Place;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;
import souther.compiler.report.GeneratedRows;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.time.Duration;
import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.function.Predicate;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTimeoutPreemptively;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A row at a point of a line on how many elements meet a statement is a container with that many
 * elements meeting it, composed for the point and read back there.
 *
 * <p>The elements are chosen against the numbers the statement reads beside them, out of values
 * grouped by what each answers of every statement asked of the container; a list may hold one value
 * twice and a set may not. A statement no element can be read for leaves the point owed and is no
 * proof the point is out of reach.
 */
class AContainerIsComposedWithSoManyElementsMeetingAStatementTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** Every point of the line has a row built for it and read back there; below none is no count
     *  at all. */
    @Test
    void everyPointOfALineOnACountHasARowComposedForIt() {
        JsonNode count = only(countBorders(reportOf("""
                module probe

                behavior exactlyOne : (xs: List<Int>, limit: Int) -> Int
                let exactlyOne (xs, limit) =
                    if List.length(List.filter(x -> x > limit, xs)) == 1 then 1 else 0
                """)));
        assertComposedAtEveryPointButBelowNone(count);
    }

    /**
     * Two counts of one container held together: a row at a point of either is a container whose
     * elements meet the other count too, since the second is reached only where the first holds.
     */
    @Test
    void twoCountsOfOneContainerAreComposedTogether() {
        List<JsonNode> counts = countBorders(reportOf("""
                module probe

                behavior oneEach : (xs: List<Int>) -> Int
                let oneEach (xs) =
                    if List.length(List.filter(x -> x > 0, xs)) == 1
                            && List.length(List.filter(x -> x < 0, xs)) == 1
                        then 1 else 0
                """));
        assertEquals(2, counts.size(), () -> "a line on each count: " + counts);
        counts.forEach(AContainerIsComposedWithSoManyElementsMeetingAStatementTest
                ::assertComposedAtEveryPointButBelowNone);
    }

    /**
     * A count reached only where some element is below nought: the element the way places and the
     * elements the count asks for are one container, composed once.
     */
    @Test
    void aCountReachedWhereSomeElementMeetsAnotherStatementIsComposedWithIt() {
        JsonNode count = only(countBorders(reportOf("""
                module probe

                behavior past : (xs: List<Int>) -> Int
                let past (xs) =
                    if List.any(x -> x < 0, xs) then
                        if List.length(List.filter(x -> x > 0, xs)) == 1 then 1 else 0
                    else 2
                """)));
        assertComposedAtEveryPointButBelowNone(count);
    }

    /** How many a container holds beside how many of them meet a statement: one container. */
    @Test
    void aCountBesideHowManyTheContainerHoldsIsComposedInOneContainer() {
        JsonNode count = only(countBorders(reportOf("""
                module probe

                behavior three : (xs: List<Int>) -> Int
                let three (xs) =
                    if List.length(xs) == 3 then
                        if List.length(List.filter(x -> x > 0, xs)) == 1 then 1 else 0
                    else 2
                """)));
        assertComposedAtEveryPointButBelowNone(count);
    }

    /** A set holds each value once, so its elements are different values. */
    @Test
    void aSetIsComposedOfDifferentValues() {
        String source = """
                module probe

                behavior two : (xs: Set<Int>) -> Int
                let two (xs) =
                    if Set.size(Set.filter(x -> x > 0, xs)) >= 2 then 1 else 0
                """;
        JsonNode count = only(countBorders(reportOf(source)));
        assertTrue(pointsAt(count, "on").getFirst().path("knownWritable").asBoolean(),
                () -> "two above nought: " + count);
        List<List<String>> sets = containersOffered(source);
        assertTrue(sets.stream().anyMatch(each -> each.size() >= 2),
                () -> "a set of two or more: " + sets);
        for (List<String> each : sets) {
            assertEquals(each.size(), each.stream().distinct().count(),
                    () -> "no value twice in a set: " + each);
        }
    }

    /**
     * A statement read over the elements of another container is one no element of the first can
     * be read for alone: the point is left owed, and nothing says the rules refuse it.
     */
    @Test
    void aStatementOverAnotherContainersElementsIsLeftOwedAndNotRefused() {
        JsonNode count = only(countBorders(reportOf("""
                module probe

                behavior fits : (ws: List<Int>, cs: List<Int>) -> Int
                let fits (ws, cs) =
                    if List.length(List.filter(w -> List.all(c -> w > c, cs), ws)) == 1
                        then 1 else 0
                """)));
        JsonNode on = pointsAt(count, "on").getFirst();
        assertFalse(on.path("knownWritable").asBoolean(), () -> "nothing composed: " + on);
        assertTrue(on.path("notOwed").isMissingNode(), () -> "and not refused: " + on);
    }

    /**
     * How many of some values written out meet a statement is which of them do: two of {@code [a,
     * a]} above nought is {@code a} above nought, a line on {@code a}.
     */
    @Test
    void aCountOfValuesWrittenOutIsALineOnWhatTheyAreWrittenWith() {
        JsonNode report = reportOf("""
                module probe

                behavior twice : (a: Int) -> Int
                let twice (a) =
                    if List.length(List.filter(x -> x > 0, [a, a])) == 2 then 1 else 0
                example twice
                    | "above" : (1) -> 1
                    | "at" : (0) -> 0
                """);
        List<JsonNode> ofTheCount = new ArrayList<>();
        collect(report, ofTheCount, node -> "twice/a".equals(node.path("axis").asString())
                && node.at("/obligationId/line/which/rule/ordinal").asInt() == 5);
        assertEquals(1, ofTheCount.size(), () -> "the count's comparison draws one line on a: "
                + ofTheCount);
        assertTrue(pointsAt(ofTheCount.getFirst(), "on").getFirst().path("hit").asBoolean(),
                "one is two values above nought");
        assertTrue(pointsAt(ofTheCount.getFirst(), "off").getFirst().path("hit").asBoolean(),
                "and nought is none");
    }

    /**
     * The numbers a statement reads beside an element are placed together, with an element that
     * meets it: an element above {@code a} and below {@code b} is there only where {@code b} is
     * two past {@code a}, which neither of them says alone.
     */
    @Test
    void theNumbersBesideAnElementArePlacedTogetherWithAnElementMeetingTheStatement() {
        JsonNode count = only(countBorders(reportOf("""
                module probe

                behavior between : (xs: List<Int>, a: Int, b: Int) -> Int
                let between (xs, a, b) =
                    if a > 5 then
                        if List.length(List.filter(x -> x > a && x < b, xs)) == 1 then 1 else 0
                    else 2
                """)));
        assertComposedAtEveryPointButBelowNone(count);
    }

    /**
     * A statement that turns over between two values an element can take still tells them apart:
     * {@code 3 * x > 1} turns at a third, which no element is, and nought fails it where one meets
     * it.
     */
    @Test
    void aStatementTurningBetweenTwoValuesStillTellsThemApart() {
        JsonNode count = only(countBorders(reportOf("""
                module probe

                behavior third : (xs: List<Int>) -> Int
                let third (xs) =
                    if List.length(List.filter(x -> 3 * x > 1, xs)) == 1 then 1 else 0
                """)));
        assertComposedAtEveryPointButBelowNone(count);
    }

    /**
     * The values an element is chosen from are the runs the rules leave it, parted where a
     * statement turns — and a place it turns at outside them parts nothing and is no value: an
     * element held between 0.34 and 0.35 is above a third and below a half whichever of those it
     * is, and one of them is chosen.
     */
    @Test
    void anElementIsChosenFromWhatTheRulesLeaveItPartedWhereTheStatementTurns() {
        ExactRatio third = ExactRatio.of(BigInteger.ONE, BigInteger.valueOf(3));
        ExactRatio half = ExactRatio.of(BigInteger.ONE, BigInteger.TWO);
        NumericDomain.Bounds held = new NumericDomain.Bounds(
                Endpoint.inclusive(Count.of(new BigDecimal("0.34"))),
                Endpoint.inclusive(Count.of(new BigDecimal("0.35"))));
        List<Place> chosen = CardinalityComposer.valuesAlong(Carrier.DENSE, held,
                List.of(third, half), 1, new LinkedHashSet<>());
        assertFalse(chosen.isEmpty(), "a value between 0.34 and 0.35 is there to choose");
        for (Place each : chosen) {
            ExactRatio at = Count.number(each).exactly();
            assertTrue(at.compareTo(ExactRatio.of(new BigDecimal("0.34"))) >= 0
                            && at.compareTo(ExactRatio.of(new BigDecimal("0.35"))) <= 0,
                    () -> "every value chosen is one the rules leave: " + chosen);
        }
    }

    /**
     * And a place it turns at inside them parts them there, however narrow the parts: an element
     * held between 0.33 and 0.34 is below a third or above it, and a value is chosen on each side.
     */
    @Test
    void aNarrowRunIsPartedWhereTheStatementTurnsInsideIt() {
        ExactRatio third = ExactRatio.of(BigInteger.ONE, BigInteger.valueOf(3));
        NumericDomain.Bounds held = new NumericDomain.Bounds(
                Endpoint.inclusive(Count.of(new BigDecimal("0.33"))),
                Endpoint.inclusive(Count.of(new BigDecimal("0.34"))));
        List<ExactRatio> chosen = CardinalityComposer.valuesAlong(Carrier.DENSE, held,
                List.of(third), 1, new LinkedHashSet<>()).stream()
                .map(each -> Count.number(each).exactly()).toList();
        assertTrue(chosen.stream().anyMatch(at -> at.compareTo(third) < 0
                        && at.compareTo(ExactRatio.of(new BigDecimal("0.33"))) >= 0),
                () -> "a value from 0.33 up to a third: " + chosen);
        assertTrue(chosen.stream().anyMatch(at -> at.compareTo(third) > 0
                        && at.compareTo(ExactRatio.of(new BigDecimal("0.34"))) <= 0),
                () -> "and one from past a third to 0.34: " + chosen);
    }

    /**
     * And between two such places closer than one step of a digit, a value is chosen, at digits
     * enough to stand between them: a thirtieth and a fifteenth, with nothing in tenths between.
     */
    @Test
    void aValueIsChosenBetweenTwoPlacesNoValueIs() {
        ExactRatio thirtieth = ExactRatio.of(BigInteger.ONE, BigInteger.valueOf(30));
        ExactRatio fifteenth = ExactRatio.of(BigInteger.ONE, BigInteger.valueOf(15));
        List<Place> chosen = CardinalityComposer.valuesAlong(Carrier.DENSE,
                NumericDomain.Bounds.OPEN, List.of(thirtieth, fifteenth), 1,
                new LinkedHashSet<>());
        assertTrue(chosen.stream().map(each -> Count.number(each).exactly())
                        .anyMatch(at -> at.compareTo(thirtieth) > 0 && at.compareTo(fifteenth) < 0),
                () -> "one value between a thirtieth and a fifteenth: " + chosen);
        assertTrue(chosen.stream().map(each -> Count.number(each).exactly())
                        .anyMatch(at -> at.compareTo(thirtieth) < 0),
                () -> "and one below the thirtieth: " + chosen);
        assertTrue(chosen.stream().map(each -> Count.number(each).exactly())
                        .anyMatch(at -> at.compareTo(fifteenth) > 0),
                () -> "and one above the fifteenth: " + chosen);
    }

    /**
     * Two conditions on one count are met where both are: past two and past three is past three,
     * and a row composed for the first alone never reaches the line under the second.
     */
    @Test
    void twoConditionsOnOneCountAreMetTogether() {
        JsonNode y = onlyLineOn(reportOf("""
                module probe

                behavior both : (xs: List<Int>, y: Int) -> Int
                let both (xs, y) =
                    if List.length(List.filter(x -> x > 0, xs)) >= 2 then
                        if List.length(List.filter(x -> x > 0, xs)) >= 3 then
                            if y > 0 then 1 else 0
                        else 2
                    else 3
                """), "both/y");
        for (JsonNode item : y.path("items")) {
            if (item.has("against")) {
                assertTrue(item.path("knownWritable").asBoolean(),
                        () -> "a row with three above nought reaches the line: " + item);
            }
        }
    }

    /**
     * A count asked for far past what a container is composed with is answered at once, and as a
     * search that stopped rather than as a way no row passes.
     */
    @Test
    void aCountFarPastAnyContainerComposedIsAnsweredAtOnce() {
        JsonNode y = assertTimeoutPreemptively(Duration.ofSeconds(30), () -> onlyLineOn(reportOf("""
                module probe

                behavior many : (xs: List<Int>, y: Int) -> Int
                let many (xs, y) =
                    if List.length(List.filter(x -> x > 0, xs)) >= 1000000000 then
                        if y > 0 then 1 else 0
                    else 2
                """), "many/y"));
        for (JsonNode item : y.path("items")) {
            assertTrue(item.path("notOwed").isMissingNode(),
                    () -> "a count no container here holds is not one the rules refuse: " + item);
        }
    }

    private static JsonNode onlyLineOn(JsonNode report, String axis) {
        List<JsonNode> out = new ArrayList<>();
        collect(report, out, node -> axis.equals(node.path("axis").asString()));
        assertEquals(1, out.size(), () -> "one line on " + axis + ": " + out);
        return out.getFirst();
    }

    private static void assertComposedAtEveryPointButBelowNone(JsonNode count) {
        for (JsonNode item : count.path("items")) {
            boolean belowNone = "out".equals(item.path("point").asString())
                    && "below".equals(item.at("/location/side").asString());
            if (belowNone) {
                assertEquals("the_rules_refuse_it", item.path("notOwed").asString(),
                        () -> "no count is below none: " + item);
                continue;
            }
            assertTrue(item.path("knownWritable").asBoolean(),
                    () -> "a row composed and read back: " + item + " of " + count.path("axis"));
            List<String> because = new ArrayList<>();
            item.path("writableBecause").forEach(each -> because.add(each.asString()));
            assertTrue(because.contains("a_value_was_built"), () -> "because one was: " + item);
        }
    }

    private static JsonNode reportOf(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        return JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
    }

    /** The values of every container the rows offered for {@code source} write. */
    private static List<List<String>> containersOffered(String source) {
        Compilation compilation = Compilation.ofSource(source, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        String rows = GeneratedRows.of(compilation, "probe", null,
                SourceRendering.namedByIdentity(SourceLayouts.NONE)).text();
        List<List<String>> out = new ArrayList<>();
        Matcher written = Pattern.compile("\\[([^\\]]*)\\]").matcher(rows);
        while (written.find()) {
            List<String> values = new ArrayList<>();
            for (String each : written.group(1).split(",")) {
                if (!each.isBlank()) {
                    values.add(each.strip());
                }
            }
            out.add(values);
        }
        return out;
    }

    private static List<JsonNode> countBorders(JsonNode report) {
        List<JsonNode> out = new ArrayList<>();
        collect(report, out, node -> "count_of_elements".equals(node.path("kind").asString()));
        return out;
    }

    private static void collect(JsonNode node, List<JsonNode> out,
                                Predicate<JsonNode> wanted) {
        if (node.isObject() && node.has("items") && wanted.test(node)) {
            out.add(node);
        }
        node.forEach(child -> collect(child, out, wanted));
    }

    private static JsonNode only(List<JsonNode> borders) {
        assertEquals(1, borders.size(), () -> "one line on the count: " + borders);
        return borders.getFirst();
    }

    private static List<JsonNode> pointsAt(JsonNode border, String point) {
        List<JsonNode> out = new ArrayList<>();
        border.path("items").forEach(each -> {
            if (point.equals(each.path("point").asString())) {
                out.add(each);
            }
        });
        if (out.isEmpty()) {
            throw new AssertionError("a " + point + " point on " + border);
        }
        return out;
    }
}
