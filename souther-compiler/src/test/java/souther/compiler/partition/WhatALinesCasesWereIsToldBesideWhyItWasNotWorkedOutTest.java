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
 * choosing one than are taken apart, a report says beside why how many ways there were and which
 * constructs of the model the statement chooses at — and that is all it adds.
 *
 * <p>The rule here finds the first of seven thresholds two numbers and their sum are all above,
 * and compares what it found: each line of it decides where every threshold before the one found
 * was missed, which is one of three comparisons failing at each, so its cases are as many ways as
 * three to the power of six. The numbers compared are one value each, so most of those ways ask
 * them to be two things at once.
 */
class WhatALinesCasesWereIsToldBesideWhyItWasNotWorkedOutTest {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    private static final String MODEL = """
            module demo exposing (g)

            behavior g : (x: Int, y: Int) -> Bool
            let g (x, y) =
                Option.withDefault(0, List.find(t -> x > t && y > t && x + y > t,
                    [1, 2, 3, 4, 5, 6, 7])) > 3
            """;

    private static Compilation compiled() {
        Compilation compilation = Compilation.ofSource(MODEL, "Main");
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

    @Test
    void eachLineNotWorkedOutForItsManyCasesSaysHowManyWaysTheyWereAndWhatChoseThem() {
        JsonNode partition = partition(compiled());
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
            JsonNode factors = counted.path("factors");
            assertEquals(1, factors.size(), "the find, and nothing named that the model did not"
                    + " write: " + factors);
            JsonNode find = factors.get(0);
            assertEquals("find", find.path("kind").asString());
            assertEquals(7, find.path("width").asInt(), "the thresholds written out");
            assertEquals("List.find", find.path("operation").asString());
            assertEquals("g", find.path("construct").path("definition").asString());
            assertEquals(each.path("ruleId"), expansions.get(0).path("ruleId"),
                    "one rule, whose lines these are");
        }
        assertEquals(Set.of("g/x", "g/y", "g/x + y"), lines, "a line of each number compared");
    }

    /**
     * Two lines of one rule are one finding about why, at a place, and two entries about what their
     * cases were: a count is the cases of one case of one line, which is put together with no
     * other.
     */
    @Test
    void theCountsOfTwoLinesAreNeverPutTogetherAsTheirReasonIs() {
        JsonNode partition = partition(compiled());
        List<String> told = new ArrayList<>();
        for (JsonNode each : partition.path("caseExpansions")) {
            told.add(each.path("line").asString() + " at most "
                    + each.path("caseExpansion").path("numericallyConsistentWays")
                            .path("atMost").asString());
        }
        assertEquals(told.size(), new TreeSet<>(told).size(), "each line and count once: " + told);
        assertTrue(told.stream().map(each -> each.substring(each.indexOf(" at most ")))
                        .distinct().count() > 1,
                "lines of one rule whose cases come to different counts keep their own: " + told);
        for (String section : List.of("notRead", "unanswered")) {
            for (JsonNode each : partition.path(section)) {
                assertFalse(each.has("caseExpansion"), "why is said with no count in it: " + each);
            }
        }
    }

    @Test
    void aPersonIsToldTheCountsAndTheConstructsAsAListAndNeverAsAProduct() {
        Compilation compilation = compiled();
        String said = AdequacyReport.of(compilation)
                .human(SourceRendering.namedByIdentity(compilation.texts()));
        List<String> lines = said.lines().filter(each -> each.contains("case expansion:"))
                .toList();
        assertFalse(lines.isEmpty(), said);
        for (String each : lines) {
            assertTrue(each.contains("729 structural ways; at most "), each);
            assertTrue(each.contains("Contributing constructs: find in g (7 elements written out)"),
                    each);
            assertFalse(each.contains("×"), "the constructs are not multiplied: " + each);
        }
    }

    /**
     * A line read on every application of a closure decides in the cases of any one of them, so
     * its cases may be too many to take apart where those of no one application are. What chose
     * them is read off every application's statement then: here a fold over a table of grades
     * reads the average of the months a filter keeps, each application in as many cases as the
     * months kept may be, and the line on what the filter asks of a month is past the figure only
     * across all of them.
     */
    @Test
    void aLineReadOnEveryApplicationNamesWhatChoseItsCasesAcrossThem() {
        StringBuilder rows = new StringBuilder();
        for (int at = 1; at <= 37; at++) {
            rows.append(at == 1 ? "" : ", ").append("Row { grade = ").append(at)
                    .append(", lowerBound = ").append((at - 1) * 100).append(" }");
        }
        Compilation compilation = Compilation.ofSource("""
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
                """.replace("ROWS", rows), "Main");
        compilation.measure(Adequacy.Asked.reportOnly(Adequacy.Level.OFF));
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors());
        JsonNode expansions = partition(compilation).path("caseExpansions");
        assertFalse(expansions.isEmpty(), "the lines past the figure across the applications");
        for (JsonNode each : expansions) {
            JsonNode factors = each.path("caseExpansion").path("factors");
            assertEquals(1, factors.size(), "the filter, named once at its call: " + factors);
            JsonNode filter = factors.get(0);
            assertEquals("filter", filter.path("kind").asString());
            assertEquals(3, filter.path("width").asInt(), "the months written out");
            assertEquals("List.filter", filter.path("operation").asString());
            assertEquals("payableMonths", filter.path("construct").path("definition").asString());
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
