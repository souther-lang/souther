package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.diag.SourceRendering;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import tools.jackson.databind.JsonNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A condition on the size or the emptiness of what {@code Set.union}, {@code Set.intersection},
 * {@code Set.difference} or {@code Set.fromList} answers is read to the end, as the same condition
 * written over the elements is.
 *
 * <p>What it says is how the values of the input stand to one another: how many of one set's
 * elements are one of another's, or how many different values a list holds. That is no number a
 * position holds, so no line is drawn on a position, and the rule is said at the values it relates —
 * which is what {@code List.all(l -> Set.contains(l.sku, shipped), lines)} is said as. None of it
 * is a rule nobody read.
 */
class TheSizeOfASetMadeOfInputsIsReadThroughItsLawTest {

    private static final String HEAD = """
            module probe.s

            data Line = { sku: String }
            data Mixed = { n: Int }

            """;

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /** What was left unread about a behavior's positions and what its measure is weakened by. */
    private record Said(List<String> notRead, List<String> weakening) {}

    private static Said of(String behavior, String name) {
        Compilation compilation = Compilation.ofSource(HEAD + behavior, "Main");
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList());
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        AdequacyReport report = AdequacyReport.of(compilation);
        List<String> notRead = new ArrayList<>();
        for (AdequacyReport.BehaviorReport each : report.modules().get(0).behaviors()) {
            if (each.name().equals(name)) {
                each.partition().notRead().forEach(one -> notRead.add(one.at() + " " + one.reason()));
            }
        }
        List<String> weakening = new ArrayList<>();
        JsonNode document = JSON.readTree(
                report.json(SourceRendering.namedByIdentity(compilation.texts())));
        for (JsonNode each : document.get("modules").get(0).get("behaviors")) {
            if (each.get("name").asString().equals(name)) {
                each.path("weakening").forEach(one -> weakening.add(one.asString()));
            }
        }
        // The order places are met in is the reading's, and says nothing about the rule.
        return new Said(notRead.stream().sorted().toList(), weakening);
    }

    private static void relatesValues(Said said, List<String> at) {
        assertEquals(at.stream().map(one -> one + " RULE_RELATING_TWO_VALUES").sorted().toList(),
                said.notRead());
        assertFalse(said.weakening().contains("rule_unread"), said.weakening().toString());
    }

    @Test
    void theSizeOfAUnionStandsTheValuesOfTwoSetsAgainstOneAnother() {
        relatesValues(of("""
                behavior f : (a: Set<String>, b: Set<String>) -> Int
                let f (a, b) = if Set.size(Set.union(a, b)) <= 1 then 1 else 0
                """, "f"), List.of("Set.size(a)", "a[*]", "b[*]"));
    }

    @Test
    void anIntersectionHoldingNothingStandsTheValuesOfTwoSetsAgainstOneAnother() {
        relatesValues(of("""
                behavior f : (a: Set<String>, b: Set<String>) -> Int
                let f (a, b) = if Set.isEmpty(Set.intersection(a, b)) then 1 else 0
                """, "f"), List.of("a[*]", "b[*]"));
    }

    @Test
    void aDifferenceHoldingNothingStandsTheValuesOfTwoSetsAgainstOneAnother() {
        relatesValues(of("""
                behavior f : (a: Set<String>, b: Set<String>) -> Int
                let f (a, b) = if Set.isEmpty(Set.difference(a, b)) then 1 else 0
                """, "f"), List.of("a[*]", "b[*]"));
    }

    @Test
    void theSizeOfASetMadeOfAListIsHowManyDifferentValuesTheListHolds() {
        relatesValues(of("""
                behavior f : (xs: List<String>) -> Int
                let f (xs) = if Set.size(Set.fromList(xs)) == 1 then 1 else 0
                """, "f"), List.of("xs[*]"));
    }

    @Test
    void theSameCountIsReadWhereAGuardAsksIt() {
        relatesValues(of("""
                behavior f : (fs: List<String>) -> Int | Mixed
                let f (fs) = {
                    guard Set.size(Set.fromList(fs)) == 1 else Mixed { n = 1 }
                    1
                }
                """, "f"), List.of("fs[*]"));
    }

    @Test
    void howManyDifferentValuesAListHoldsIsReadWhateverWayItIsAsked() {
        relatesValues(of("""
                behavior f : (xs: List<String>) -> Int
                let f (xs) = if List.length(List.distinct(xs)) >= 2 then 1 else 0
                """, "f"), List.of("xs[*]"));
    }

    /**
     * What a call answering a truth inside the closure states is its own, and the emptiness check
     * around it does not state it a second time.
     */
    @Test
    void aRelationAClosureStatesIsNotStatedAgainByTheCheckAroundIt() {
        relatesValues(of("""
                behavior f : (xs: List<String>, ys: List<String>) -> Int
                let f (xs, ys) =
                    if List.isEmpty(List.filter(x -> List.contains(x, ys), xs)) then 1 else 0
                """, "f"), List.of("xs[*]", "ys[*]"));
    }

    @Test
    void aDifferenceOfWhatAProjectionOfAListComesToIsReadAsItsElementsAre() {
        Said throughASet = of("""
                behavior f : (lines: List<Line>, shipped: Set<String>) -> Int
                let f (lines, shipped) =
                    if Set.isEmpty(Set.difference(Set.fromList(List.map(.sku, lines)), shipped))
                    then 1 else 0
                """, "f");
        Said overTheElements = of("""
                behavior f : (lines: List<Line>, shipped: Set<String>) -> Int
                let f (lines, shipped) =
                    if List.all(l -> Set.contains(l.sku, shipped), lines) then 1 else 0
                """, "f");

        assertEquals(overTheElements, throughASet);
        relatesValues(throughASet, List.of("shipped[*]", "lines[*].sku"));
    }
}
