package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.io.IOException;
import java.io.InputStream;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Where a line of a rule is not worked out because the cases where it decides are more ways of
 * choosing one than are taken apart, a report says beside why how many ways each case was and what
 * in the model made the parts it is taken apart on — and that is all it adds.
 *
 * <p>The first rule here finds the first of seven thresholds two numbers and their sum are all
 * above, and compares what it found: each line of it decides where every threshold before the one
 * found was missed, which is one of three comparisons failing at each, so its cases are as many
 * ways as three to the power of six. Every part is a comparison the search's closure makes on one
 * of its applications. The numbers compared are one value each, so most of those ways ask them to
 * be two things at once.
 */
class WhatALinesCasesWereIsToldBesideWhyItWasNotWorkedOutTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String FIND = """
            module demo exposing (g)

            behavior g : (x: Int, y: Int) -> Bool
            let g (x, y) =
                Option.withDefault(0, List.find(t -> x > t && y > t && x + y > t,
                    [1, 2, 3, 4, 5, 6, 7])) > 3
            """;

    /** A table of {@code rows} grades, each bound a hundred above the one before. */
    private static String gradeTable(int rows) {
        StringBuilder out = new StringBuilder();
        for (int at = 1; at <= rows; at++) {
            out.append(at == 1 ? "" : ", ").append("Row { grade = ").append(at)
                    .append(", lowerBound = ").append((at - 1) * 100).append(" }");
        }
        return out.toString();
    }

    private static Compilation compiled(String model) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.OFF));
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors());
        return compilation;
    }

    private static JsonNode partition(Compilation compilation) {
        JsonNode report = JSON.readTree(AdequacyReport.of(compilation)
                .json(SourceRendering.namedByIdentity(compilation.texts())));
        return report.path("modules").get(0).path("behaviors").get(0).path("partition");
    }

    /**
     * What {@code model} has written from where {@code construct}'s place is to the end of its
     * line, so that a place is held to the construct and not to a number.
     */
    private static String writtenAt(String model, JsonNode construct) {
        JsonNode at = construct.path("at");
        assertTrue(at.has("line") && at.has("column"),
                "where the author wrote it, as a line and a column: " + construct);
        String line = model.lines().toList().get(at.path("line").asInt() - 1);
        return line.substring(at.path("column").asInt() - 1);
    }

    /** What {@code entry}'s case came to, read at one copy of its rule, which every model here
     *  that writes its rule outside a helper reads it at. */
    private static JsonNode onlyReading(JsonNode entry) {
        JsonNode readings = entry.path("readings");
        assertEquals(1, readings.size(), "one copy of the rule, one reading: " + entry);
        return readings.get(0).path("caseExpansion");
    }

    /** The factors of {@code kind} in {@code factors}. */
    private static List<JsonNode> ofKind(JsonNode factors, String kind) {
        List<JsonNode> out = new ArrayList<>();
        factors.forEach(each -> {
            if (each.path("kind").asString().equals(kind)) {
                out.add(each);
            }
        });
        return out;
    }

    @Test
    void eachLineNotWorkedOutForItsManyCasesSaysHowManyWaysTheyWereAndWhatMadeThem() {
        JsonNode partition = partition(compiled(FIND));
        JsonNode expansions = partition.path("caseExpansions");
        assertFalse(expansions.isEmpty(), "the lines past the cases taken apart are told of: "
                + partition);
        BigInteger structural = BigInteger.valueOf(3).pow(6);
        Set<String> lines = new TreeSet<>();
        for (JsonNode each : expansions) {
            lines.add(each.path("line").asString());
            JsonNode counted = onlyReading(each);
            assertEquals(structural.toString(),
                    counted.path("structuralWays").path("exactly").asString(),
                    "every way of choosing, three failing comparisons at each of six thresholds");
            BigInteger consistent = new BigInteger(
                    counted.path("numericallyConsistentWays").path("atMost").asString());
            assertTrue(consistent.signum() > 0 && consistent.compareTo(structural) < 0,
                    "no more ways than there are, and fewer: a number is one value " + each);
            assertEquals(0, counted.path("unattributed").asInt(),
                    "every part is a comparison an application of the search made: " + counted);
            JsonNode factors = counted.path("factors");
            assertEquals(1, factors.size(), "the search, and nothing named that the model did not"
                    + " write — the && is no choice, and the match in Option.withDefault is the"
                    + " library's: " + factors);
            JsonNode find = factors.get(0);
            assertEquals("applications", find.path("kind").asString());
            assertEquals("List.find", find.path("operation").asString());
            assertEquals(7, find.path("applications").asInt(), "one on each threshold");
            assertEquals("g", find.path("call").path("definition").asString());
            assertTrue(writtenAt(FIND, find).startsWith("List.find("),
                    "at the call the author wrote: " + find);
            assertEquals(each.path("ruleId"), expansions.get(0).path("ruleId"),
                    "one rule, whose lines these are");
            for (JsonNode diagnosis : counted.path("diagnosed")) {
                assertEquals("orderedBoundaries", diagnosis.path("kind").asString(),
                        "no remainder is compared: " + diagnosis);
                assertTrue(Set.of("x", "y", "x + y").contains(
                        diagnosis.path("quantity").asString()), diagnosis::toString);
                assertEquals(diagnosis.path("points").asInt() + 1,
                        diagnosis.path("waysAtMost").asInt(), diagnosis::toString);
                assertTrue(diagnosis.path("points").asInt() <= 7,
                        "a point at each threshold at most: " + diagnosis);
            }
            assertFalse(counted.path("diagnosed").isEmpty(),
                    "the thresholds of each number tie its comparisons: " + counted);
        }
        assertEquals(Set.of("g/x", "g/y", "g/x + y"), lines, "a line of each number compared");
    }

    /** Where an entry's line is: the quantity, where on it, and which of the author's lines. */
    private static String placeOf(JsonNode entry) {
        return entry.path("line").asString() + " at " + entry.path("cutAt").asString() + " "
                + entry.path("arms");
    }

    /**
     * Two lines of one rule are one finding about why, at a place, and an entry for each case of
     * each place: a count is the cases of one case of one line, which is put together with no
     * other. Here the comparison is read on each arm of the default the search's answer is taken
     * through, so each line the author wrote comes to the same relation twice, once on each arm —
     * two places, with the same quantity, the same level and the same counts, told apart only by
     * the arms; and two lines on the sum at two thresholds are two places as well.
     */
    @Test
    void theCountsOfTwoPlacesOfALineAreNeverPutTogetherAsTheirReasonIs() {
        JsonNode partition = partition(compiled(FIND));
        List<String> told = new ArrayList<>();
        List<String> came = new ArrayList<>();
        Set<String> levels = new TreeSet<>();
        for (JsonNode each : partition.path("caseExpansions")) {
            told.add(placeOf(each) + " case " + each.path("case").asInt() + " of "
                    + each.path("casesOfTheLine").asInt());
            came.add(each.path("line").asString() + " " + onlyReading(each));
            levels.add(each.path("line").asString() + " at " + each.path("cutAt").asString());
        }
        assertEquals(told.size(), new TreeSet<>(told).size(), "each case of each place once: "
                + told);
        assertTrue(levels.size() < told.size(),
                "places of one quantity at one level, told apart by the author's arms: " + told);
        assertTrue(came.size() > new TreeSet<>(came).size(),
                "places that came to the same are two entries still: " + came);
        // And numbered among their own place's cases only: another place on the same quantity,
        // at the same level or another, counts none of them.
        java.util.Map<String, List<Integer>> numbered = new java.util.TreeMap<>();
        java.util.Map<String, Integer> claimed = new java.util.TreeMap<>();
        for (JsonNode each : partition.path("caseExpansions")) {
            String line = placeOf(each);
            numbered.computeIfAbsent(line, _ -> new ArrayList<>()).add(each.path("case").asInt());
            claimed.put(line, each.path("casesOfTheLine").asInt());
        }
        numbered.forEach((line, cases) -> {
            assertEquals(cases.size(), claimed.get(line), "the cases of " + line);
            assertEquals(java.util.stream.IntStream.rangeClosed(1, cases.size()).boxed()
                    .toList(), cases, "numbered from one: " + line);
        });
        for (String section : List.of("notRead", "unanswered")) {
            for (JsonNode each : partition.path(section)) {
                assertFalse(each.has("readings") || each.has("caseExpansion"),
                        "why is said with no count in it: " + each);
            }
        }
    }

    /** The search of {@link #FIND} written in a helper, which the behavior calls on each arm. */
    private static final String FIND_IN_A_HELPER_CALLED_TWICE = """
            module demo exposing (g)

            let h (x: Int, y: Int): Bool =
                Option.withDefault(0, List.find(t -> x > t && y > t && x + y > t,
                    [1, 2, 3, 4, 5, 6, 7])) > 3

            behavior g : (b: Bool, x: Int, y: Int) -> Bool
            let g (b, x, y) = if b then h(x, y) else h(x, y)
            """;

    /**
     * A rule written in a helper is read once for each call, and both calls here hand it the same
     * values, so each of its cases is the same case at both: one entry, numbered among its line's
     * cases as though the helper were called once, with what it came to at each call — where what
     * made its parts is that call's copy of the search.
     */
    @Test
    void aCaseReadAtEachCallOfAHelperIsOneCaseWithAReadingAtEach() {
        JsonNode expansions = partition(compiled(FIND_IN_A_HELPER_CALLED_TWICE))
                .path("caseExpansions");
        assertFalse(expansions.isEmpty(), "the helper's lines past the figure");
        for (JsonNode each : expansions) {
            assertEquals(1, each.path("casesOfTheLine").asInt(),
                    "one case of each place, whichever call it was read in: " + each);
            JsonNode readings = each.path("readings");
            assertEquals(2, readings.size(), "an answer at each call: " + each);
            Set<String> copies = new TreeSet<>();
            Set<String> searches = new TreeSet<>();
            for (JsonNode reading : readings) {
                assertEquals(1, reading.path("readAt").size(), reading::toString);
                copies.add(reading.path("readAt").get(0).toString());
                JsonNode find = reading.path("caseExpansion").path("factors").get(0);
                assertEquals("List.find", find.path("operation").asString());
                searches.add(find.path("call").toString());
                assertTrue(writtenAt(FIND_IN_A_HELPER_CALLED_TWICE, find)
                        .startsWith("List.find("), "the one search the author wrote: " + find);
            }
            assertEquals(2, copies.size(), "read at the two calls: " + readings);
            assertEquals(2, searches.size(), "each naming its own call's copy: " + readings);
        }
    }

    @Test
    void aPersonIsToldTheCountsAndWhatMadeThePartsAsAListAndNeverAsAProduct() {
        Compilation compilation = compiled(FIND);
        String said = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        List<String> lines = said.lines().filter(each -> each.contains("case expansion:"))
                .toList();
        assertFalse(lines.isEmpty(), said);
        for (String each : lines) {
            assertTrue(each.contains("729 structural ways; at most "), each);
            assertTrue(each.contains(
                    "Its parts were made by: the call of List.find in g, at 5:27, on 7"
                            + " applications"),
                    each);
            assertFalse(each.contains("×"), "what made them is not multiplied: " + each);
        }
    }

    /** Enough grades for the line on what the table is looked up as to be past the figure, which
     *  twenty are not. */
    private static final int GRADES = 25;

    /**
     * A fold over a table of grades whose step is an {@code if}, read through by a comparison of
     * the grade it ends with: the cases are taken apart on the bound of each row, one on each
     * application of the step. The fold is named as the call whose applications those are, with as
     * many applications as the table has rows, and the {@code if} as a choice between two made once
     * on each application — two ways chosen many times, never many ways chosen once.
     */
    @Test
    void aFoldIsNamedByItsApplicationsAndTheChoiceInItsStepByHowOftenItIsMade() {
        String model = """
                module demo exposing (g)

                data Row = { grade: Int, lowerBound: Int }

                let gradeTable = [ ROWS ]

                let gradeFor (monthly: Int): Int =
                    List.fold((acc, r) -> if r.lowerBound <= monthly then r else acc,
                              Row { grade = 1, lowerBound = 0 }, gradeTable).grade

                behavior g : (a: Int, h: Int) -> Bool
                let g (a, h) = Int.abs(gradeFor(a) - h) < 2
                """.replace("ROWS", gradeTable(GRADES));
        JsonNode expansions = partition(compiled(model)).path("caseExpansions");
        assertFalse(expansions.isEmpty(), "the line on the grade is past the figure");
        for (JsonNode each : expansions) {
            JsonNode factors = onlyReading(each).path("factors");
            List<JsonNode> applied = ofKind(factors, "applications");
            assertEquals(1, applied.size(), "the fold, once: " + factors);
            assertEquals("List.fold", applied.getFirst().path("operation").asString(),
                    "as the author wrote it, and not what the library rewrote it to");
            assertEquals(GRADES, applied.getFirst().path("applications").asInt(),
                    "one application on each row: " + factors);
            assertEquals("gradeFor", applied.getFirst().path("call").path("definition")
                    .asString());
            assertTrue(writtenAt(model, applied.getFirst()).startsWith("List.fold("),
                    "at the fold in the helper, which every copy of it is: " + factors);
            List<JsonNode> chosen = ofKind(factors, "choice");
            JsonNode iff = chosen.stream()
                    .filter(one -> one.path("choice").asString().equals("if")).findFirst()
                    .orElseThrow(() -> new AssertionError("the if in the step: " + factors));
            assertTrue(writtenAt(model, iff).startsWith("if r.lowerBound <= monthly"),
                    "at the if the author wrote: " + iff);
            assertEquals(2, iff.path("alternatives").asInt(), "an if chooses between two");
            assertTrue(iff.path("times").asInt() > 1 && iff.path("times").asInt() <= GRADES,
                    "chosen on the applications whose bounds the case is taken apart on: " + iff);
            JsonNode abs = chosen.stream().filter(one -> one.path("choice").asString()
                            .equals("cases") && one.path("operation").asString().equals("Int.abs")
                            && one.path("alternatives").asInt() == 2).findFirst()
                    .orElseThrow(() -> new AssertionError(
                            "and the cases of the absolute value, between two: " + factors));
            assertTrue(writtenAt(model, abs).startsWith("Int.abs("),
                    "at the call whose cases they are: " + abs);
            assertEquals(0, onlyReading(each).path("unattributed").asInt(),
                    "every part made by one of them: " + each);
        }
    }

    /**
     * A line read on every application of a closure decides in the cases of any one of them, so
     * its cases may be too many to take apart where those of no one application are. What made
     * them is read off every application's statement then: here a fold over a table of grades
     * reads the average of the months a filter keeps, each application in as many cases as the
     * months kept may be. The fold is named by its applications; the filter, written outside the
     * fold, by those of its own whose truths the case is taken apart on, and not once more for
     * each application of the fold that reads what it kept; and the ways it keeps the months, seven
     * of them, written out once on each of the fold's applications.
     */
    @Test
    void aLineReadOnEveryApplicationNamesWhatMadeItsCasesAcrossThem() {
        String model = """
                module demo exposing (g, R, W)

                data R = { paidBaseDays: Int, pay: Int }
                data W = { first: R, second: R, third: R }
                data Row = { grade: Int, lowerBound: Int }

                let gradeTable = [ ROWS ]

                let payableMonths (w: W): List<R> =
                    List.filter(r -> r.paidBaseDays >= 17, [w.first, w.second, w.third])

                let gradeFor (monthly: Int): Int =
                    List.fold((acc, r) -> if r.lowerBound <= monthly then r else acc,
                              Row { grade = 1, lowerBound = 0 }, gradeTable).grade

                behavior g : (w: W) -> Int | Bool
                let g (w) = {
                    let payable = payableMonths(w)
                    guard List.length(payable) >= 1 else false
                    gradeFor(Rational.toInt(DOWN, List.sum(List.map(r -> r.pay, payable))
                            / List.length(payable)))
                }
                """.replace("ROWS", gradeTable(37));
        JsonNode expansions = partition(compiled(model)).path("caseExpansions");
        assertFalse(expansions.isEmpty(), "the lines past the figure across the applications");
        for (JsonNode each : expansions) {
            JsonNode factors = onlyReading(each).path("factors");
            List<JsonNode> applied = ofKind(factors, "applications");
            JsonNode fold = applied.stream()
                    .filter(one -> one.path("operation").asString().equals("List.fold"))
                    .findFirst().orElseThrow(() -> new AssertionError("the fold: " + factors));
            assertEquals(37, fold.path("applications").asInt(), "one on each row");
            JsonNode filter = applied.stream()
                    .filter(one -> one.path("operation").asString().equals("List.filter"))
                    .findFirst().orElseThrow(() -> new AssertionError("the filter: " + factors));
            assertEquals("payableMonths", filter.path("call").path("definition").asString());
            assertTrue(writtenAt(model, fold).startsWith("List.fold("), fold::toString);
            assertTrue(writtenAt(model, filter).startsWith("List.filter("),
                    "at the filter in the helper, not at the call of the helper: " + filter);
            assertEquals(2, filter.path("applications").asInt(),
                    "the two months besides the one the line is on, whose truths the case is"
                            + " taken apart on — read again on every application of the fold and"
                            + " still the same two applications: " + filter);
            List<JsonNode> kept = ofKind(factors, "keptWays");
            assertEquals(1, kept.size(), "the ways the months are kept: " + factors);
            assertEquals(7, kept.getFirst().path("ways").asInt(),
                    "every way of keeping some of three months");
            JsonNode keptBy = kept.getFirst().path("keptBy");
            assertEquals(1, keptBy.size(), "the filter's one condition: " + keptBy);
            assertTrue(writtenAt(model, keptBy.get(0)).startsWith(">= 17"),
                    "at the comparison that keeps a month: " + keptBy);
            assertEquals(37, kept.getFirst().path("times").asInt(),
                    "written out on each application of the fold, against its row's bound");
            assertEquals(0, onlyReading(each).path("unattributed").asInt(),
                    "every part made by one of them: " + each);
        }
    }

    /** A document of the version before, which has no such entries, is one this one reads. */
    @Test
    void theEntriesAreNoFieldADocumentMustHave() throws IOException {
        try (InputStream in = AdequacyReport.class.getResourceAsStream(
                "/souther/adequacy-schema-" + AdequacyReport.SCHEMA_VERSION + ".json")) {
            JsonNode required = JSON.readTree(in).path("$defs").path("partition")
                    .path("required");
            List<String> names = new ArrayList<>();
            required.forEach(each -> names.add(each.asString()));
            assertTrue(names.contains("notRead"), names.toString());
            assertFalse(names.contains("caseExpansions"), names.toString());
        }
    }
}
