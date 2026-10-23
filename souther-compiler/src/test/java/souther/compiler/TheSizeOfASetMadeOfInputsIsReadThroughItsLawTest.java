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
import static org.junit.jupiter.api.Assertions.assertTrue;

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

    /**
     * What a row writes says whether an element of one set is equal to an element of the other, so
     * the size of the union is the size of one set and how many elements of the other are in none
     * of its: a count over the row, which is a line, and only the size of the set it is added to is
     * left, related to that count, which is not shown to reach every value beside it.
     */
    @Test
    void theSizeOfAUnionIsTheSizeOfOneSetAndHowManyOfTheOthersElementsAreNotInIt() {
        Said said = of("""
                behavior f : (a: Set<String>, b: Set<String>) -> Int
                let f (a, b) = if Set.size(Set.union(a, b)) <= 1 then 1 else 0
                """, "f");

        assertEquals(List.of("Set.size(a) RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE"),
                said.notRead());
        assertTrue(said.weakening().contains("rule_unread"), said.weakening().toString());
    }

    /**
     * And what the line counts is the union's size as the language computes it: an element in both
     * sets is one, so the same two sets answer by how many are not in the other.
     */
    @Test
    void theCountIsTheUnionsSizeWhetherOrNotTheSetsShareAnElement() {
        Compilation compilation = Compilation.ofSource(HEAD + """
                behavior g : (a: Set<String>, b: Set<String>) -> Int
                let g (a, b) = if Set.size(Set.union(a, b)) <= 1 then 1 else 0

                example g
                    | "both empty" : ([], []) -> 1
                    | "one element in both" : (["x"], ["x"]) -> 1
                    | "two different elements" : (["x"], ["y"]) -> 0
                    | "the second inside the first" : (["x", "y"], ["x"]) -> 0
                    | "the first inside the second" : (["x"], ["x", "y"]) -> 0
                    | "the second empty" : (["x"], []) -> 1
                    | "the first empty" : ([], ["y"]) -> 1
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList());
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

    @Test
    void howManyDifferentValuesAProjectionOfAListComesToIsAskedOfTheListItIsTakenOf() {
        String model = """
                data Forecast = { currency: String, amount: Int }

                behavior %s : (fs: List<Forecast>) -> Int
                let %s (fs) = if %s then 1 else 0
                """;
        for (String condition : List.of(
                "Set.size(Set.fromList(List.map(.currency, fs))) == 1",
                "List.length(List.distinct(List.map(.currency, fs))) == 1",
                "List.length(List.distinct(List.map(f -> f.currency, fs))) == 1")) {
            relatesValues(of(model.formatted("f", "f", condition), "f"),
                    List.of("fs[*].currency"));
        }
    }

    @Test
    void theSameCountOfAProjectionIsReadWhereAGuardAsksIt() {
        relatesValues(of("""
                data Forecast = { currency: String, amount: Int }

                behavior f : (fs: List<Forecast>) -> Int | Mixed
                let f (fs) = {
                    guard Set.size(Set.fromList(List.map(.currency, fs))) == 1 else Mixed { n = 1 }
                    1
                }
                """, "f"), List.of("fs[*].currency"));
    }

    /**
     * Only what is read is said to be read: of a value worked out of each element, the number is
     * no number of the container and the rule stays a rule nobody read. Of the elements a filter
     * kept, it is how many different values those hold, which is a line of its own
     * ({@code partition.HowManyDifferentValuesMeetingAStatementIsALineOnTheCountTest}).
     */
    @Test
    void aProjectionOfAValueWorkedOutOfEachIsStillARuleNobodyRead() {
        String model = """
                data Forecast = { currency: String, amount: Int }

                behavior f : (fs: List<Forecast>) -> Int
                let f (fs) = if %s then 1 else 0
                """;
        Said worked = of(model.formatted(
                "Set.size(Set.fromList(List.map(f -> f.amount + 1, fs))) == 1"), "f");
        assertEquals(List.of("rule_unread"), worked.weakening());
        Said kept = of(model.formatted("Set.size(Set.fromList(List.map(.currency,"
                + " List.filter(f -> f.amount > 0, fs)))) == 1"), "f");
        assertFalse(kept.weakening().contains("rule_unread"), kept.weakening().toString());
    }

    /**
     * A walk adding each value it is handed to a set, or filing each under a key, ends with as many
     * as there are different values among them, and those are read down the list it walks: a map
     * taking a place out of each element, or the lists inside each element put end to end. A step
     * written as a helper's call is the helper's body, its parameters standing for what it was
     * handed.
     */
    @Test
    void howManyDifferentValuesAWalkGathersIsAskedOfWhatItsListIsTakenOf() {
        String model = """
                data Forecast = { currency: String, amount: Int }
                data Desk = { forecasts: List<Forecast> }

                let filed (cs: List<String>): Map<String, Int> =
                    List.fold((acc, c) -> Map.updateOrInsert(c, 1, n -> n + 1, acc), Map.empty, cs)

                let added (acc: Set<String>, f: Forecast): Set<String> = Set.insert(f.currency, acc)

                let bumped (acc: Map<String, Int>, f: Forecast): Map<String, Int> =
                    Map.updateOrInsert(f.currency, 1, n -> n + 1, acc)

                let byCurrency (fs: List<Forecast>): Map<String, Int> =
                    List.fold((acc, f) -> bumped(acc, f), Map.empty, fs)

                behavior f : (fs: List<Forecast>, desks: List<Desk>) -> Int
                let f (fs, desks) = if %s then 1 else 0
                """;
        for (String condition : List.of(
                "Set.size(List.fold((acc, c) -> Set.insert(c, acc), Set.empty,"
                        + " List.map(.currency, fs))) == 1",
                "Set.size(List.fold((acc, f) -> added(acc, f), Set.empty, fs)) == 1",
                "Map.size(byCurrency(fs)) == 1",
                "Map.size(filed(List.map(f -> f.currency, fs))) == 1")) {
            relatesValues(of(model.formatted(condition), "f"), List.of("fs[*].currency"));
        }
        for (String condition : List.of(
                "Set.size(List.fold((acc, c) -> Set.insert(c, acc), Set.empty,"
                        + " List.flatMap(d -> List.map(.currency, d.forecasts), desks))) == 1",
                "Map.size(filed(List.flatMap(d -> List.map(.currency, d.forecasts), desks))) == 1",
                // However many steps the closure's answer is read down to the list it stands for.
                "Map.size(filed(List.flatMap(d -> " + "List.reverse(".repeat(16)
                        + "List.map(.currency, d.forecasts)" + ")".repeat(16) + ", desks))) == 1")) {
            relatesValues(of(model.formatted(condition), "f"),
                    List.of("desks[*].forecasts[*].currency"));
        }
    }

    /**
     * And only what is read is said to be read there too: a walk over a value worked out of each
     * element gathers no place's values, and one over the lists inside each element of an outer
     * list gathers some of the occurrences of the place. A walk over the elements a filter kept
     * gathers how many different values meet a statement, and how many keys of a map a statement
     * keeps is how many keys have a gathered value meeting it: both are read, as lines of their
     * own ({@code partition.HowManyDifferentValuesMeetingAStatementIsALineOnTheCountTest}).
     */
    @Test
    void aWalkGatheringAValueWorkedOutOfEachIsStillARuleNobodyRead() {
        String model = """
                data Forecast = { currency: String, amount: Int }

                let filed (cs: List<String>): Map<String, Int> =
                    List.fold((acc, c) -> Map.updateOrInsert(c, 1, n -> n + 1, acc), Map.empty, cs)

                behavior f : (fs: List<Forecast>) -> Int
                let f (fs) = if %s then 1 else 0
                """;
        Said worked = of(model.formatted(
                "Set.size(List.fold((acc, f) -> Set.insert(f.amount + 1, acc), Set.empty, fs))"
                        + " == 1"), "f");
        assertEquals(List.of("rule_unread"), worked.weakening());
        for (String condition : List.of(
                "Set.size(List.fold((acc, f) -> Set.insert(f.currency, acc), Set.empty,"
                        + " List.filter(f -> f.amount > 0, fs))) == 1",
                "Map.size(filed(List.map(.currency, List.filter(f -> f.amount > 0, fs)))) == 1",
                "Map.size(Map.filterEntries((_, n) -> n > 0, filed(List.map(.currency, fs)))) >= 2")) {
            Said said = of(model.formatted(condition), "f");
            assertFalse(said.weakening().contains("rule_unread"), condition + " " + said);
        }
        // A walk over the lists inside one element of an outer list gathers some of the
        // occurrences of the place, and no number of them all.
        Said inEachFloor = of("""
                data Forecast = { currency: String, amount: Int }
                data Desk = { forecasts: List<Forecast> }
                data Floor = { desks: List<Desk> }

                behavior f : (floors: List<Floor>) -> List<Bool>
                let f (floors) = List.map(l -> Set.size(List.fold((acc, c) -> Set.insert(c, acc),
                    Set.empty, List.flatMap(d -> List.map(.currency, d.forecasts), l.desks))) == 1,
                        floors)
                """, "f");
        assertEquals(List.of("rule_unread"), inEachFloor.weakening());
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
        relatesValues(of("""
                behavior f : (xs: List<String>, shipped: Set<String>) -> Int
                let f (xs, shipped) =
                    if List.isEmpty(List.filter(x -> Set.contains(x, shipped), xs)) then 1 else 0
                """, "f"), List.of("xs[*]", "shipped[*]"));
    }

    /** And a comparison the closure writes keeps its own rule, as it did. */
    @Test
    void aComparisonAClosureWritesIsStillItsOwnRule() {
        Said said = of("""
                behavior f : (xs: List<Int>) -> Int
                let f (xs) = if List.isEmpty(List.filter(x -> x > 0, xs)) then 1 else 0
                """, "f");
        assertEquals(List.of(), said.notRead());
        assertEquals(List.of(), said.weakening());
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
