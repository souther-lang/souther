package souther.compiler.partition;

import org.junit.jupiter.api.Test;
import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import souther.compiler.diag.SourceLayouts;
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
                .json(SourceRendering.namedByIdentity(SourceLayouts.NONE)));
        return report.path("modules").get(0).path("behaviors").get(0).path("partition");
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
            JsonNode counted = each.path("caseExpansion");
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
            assertEquals(each.path("ruleId"), expansions.get(0).path("ruleId"),
                    "one rule, whose lines these are");
        }
        assertEquals(Set.of("g/x", "g/y", "g/x + y"), lines, "a line of each number compared");
    }

    /**
     * Two lines of one rule are one finding about why, at a place, and an entry for each case of
     * each: a count is the cases of one case of one line, which is put together with no other —
     * not even with another case of the same line that came to the same counts and the same
     * makers. Here the line on the sum is asked in two cases that come to the same.
     */
    @Test
    void theCountsOfTwoCasesAreNeverPutTogetherAsTheirReasonIs() {
        JsonNode partition = partition(compiled(FIND));
        List<String> told = new ArrayList<>();
        List<String> came = new ArrayList<>();
        for (JsonNode each : partition.path("caseExpansions")) {
            String line = each.path("line").asString();
            told.add(line + " case " + each.path("case").asInt() + " of "
                    + each.path("casesOfTheLine").asInt());
            came.add(line + " " + each.path("caseExpansion"));
        }
        assertEquals(told.size(), new TreeSet<>(told).size(), "each case of each line once: "
                + told);
        assertTrue(came.size() > new TreeSet<>(came).size(),
                "two cases of one line that came to the same are two entries still: " + came);
        for (String section : List.of("notRead", "unanswered")) {
            for (JsonNode each : partition.path(section)) {
                assertFalse(each.has("caseExpansion"), "why is said with no count in it: " + each);
            }
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
                    "Its parts were made by: the call of List.find in g, on 7 applications"),
                    each);
            assertFalse(each.contains("×"), "what made them is not multiplied: " + each);
        }
    }

    /** The fewest grades a table may have for the line on what it is looked up as to be past the
     *  figure. */
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
        JsonNode expansions = partition(compiled("""
                module demo exposing (g)

                data Row = { grade: Int, lowerBound: Int }

                let gradeTable = [ ROWS ]

                let gradeFor (monthly: Int): Int =
                    List.fold((acc, r) -> if r.lowerBound <= monthly then r else acc,
                              Row { grade = 1, lowerBound = 0 }, gradeTable).grade

                behavior g : (a: Int, h: Int) -> Bool
                let g (a, h) = Int.abs(gradeFor(a) - h) < 2
                """.replace("ROWS", gradeTable(GRADES)))).path("caseExpansions");
        assertFalse(expansions.isEmpty(), "the line on the grade is past the figure");
        for (JsonNode each : expansions) {
            JsonNode factors = each.path("caseExpansion").path("factors");
            List<JsonNode> applied = ofKind(factors, "applications");
            assertEquals(1, applied.size(), "the fold, once: " + factors);
            assertEquals("List.fold", applied.getFirst().path("operation").asString(),
                    "as the author wrote it, and not what the library rewrote it to");
            assertEquals(GRADES, applied.getFirst().path("applications").asInt(),
                    "one application on each row: " + factors);
            assertEquals("gradeFor", applied.getFirst().path("call").path("definition")
                    .asString());
            List<JsonNode> chosen = ofKind(factors, "choice");
            JsonNode iff = chosen.stream()
                    .filter(one -> one.path("choice").asString().equals("if")).findFirst()
                    .orElseThrow(() -> new AssertionError("the if in the step: " + factors));
            assertEquals(2, iff.path("alternatives").asInt(), "an if chooses between two");
            assertTrue(iff.path("times").asInt() > 1 && iff.path("times").asInt() <= GRADES,
                    "chosen on the applications whose bounds the case is taken apart on: " + iff);
            assertTrue(chosen.stream().anyMatch(one -> one.path("choice").asString()
                            .equals("cases") && one.path("operation").asString().equals("Int.abs")
                            && one.path("alternatives").asInt() == 2),
                    "and the cases of the absolute value, between two: " + factors);
            assertEquals(0, each.path("caseExpansion").path("unattributed").asInt(),
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
        JsonNode expansions = partition(compiled("""
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
                """.replace("ROWS", gradeTable(37)))).path("caseExpansions");
        assertFalse(expansions.isEmpty(), "the lines past the figure across the applications");
        for (JsonNode each : expansions) {
            JsonNode factors = each.path("caseExpansion").path("factors");
            List<JsonNode> applied = ofKind(factors, "applications");
            JsonNode fold = applied.stream()
                    .filter(one -> one.path("operation").asString().equals("List.fold"))
                    .findFirst().orElseThrow(() -> new AssertionError("the fold: " + factors));
            assertEquals(37, fold.path("applications").asInt(), "one on each row");
            JsonNode filter = applied.stream()
                    .filter(one -> one.path("operation").asString().equals("List.filter"))
                    .findFirst().orElseThrow(() -> new AssertionError("the filter: " + factors));
            assertEquals("payableMonths", filter.path("call").path("definition").asString());
            assertTrue(filter.path("applications").asInt() <= 3,
                    "of the three months it is handed, read again on every application of the"
                            + " fold and still the same applications: " + filter);
            List<JsonNode> kept = ofKind(factors, "keptWays");
            assertEquals(1, kept.size(), "the ways the months are kept: " + factors);
            assertEquals(7, kept.getFirst().path("ways").asInt(),
                    "every way of keeping some of three months");
            assertEquals(37, kept.getFirst().path("times").asInt(),
                    "written out on each application of the fold, against its row's bound");
            assertEquals(0, each.path("caseExpansion").path("unattributed").asInt(),
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
