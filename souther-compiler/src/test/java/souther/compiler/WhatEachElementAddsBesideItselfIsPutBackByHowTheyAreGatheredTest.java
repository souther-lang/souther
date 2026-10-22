package souther.compiler;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A number a walk computes of each element that adds a number of the input standing the same for
 * every element ({@link souther.compiler.inputs.ElementComputation}) is read as what the element
 * comes to and that number beside it, and what the walk gathers of them puts the number back as
 * the gathering does: once to the least or the greatest of each key.
 *
 * <p>Said of the report: the number beside is a value the rule is about, so it is named where the
 * rule relates it, and the end of each key is what the element comes to alone. A reading that
 * dropped the number would leave a rule about the end alone, and one that did not read it would
 * leave the elements a value worked out of them.
 */
class WhatEachElementAddsBesideItselfIsPutBackByHowTheyAreGatheredTest {

    private static final String HEAD = """
            module probe.beside

            data Num = { key: String, n: Int, m: Int, flag: Bool }
            data Report = { stale: List<String> }

            """;

    private static List<String> notRead(String behavior) {
        Compilation compilation = Compilation.ofSource(HEAD + behavior, "Main");
        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList());
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        List<String> said = new ArrayList<>();
        for (AdequacyReport.BehaviorReport each :
                AdequacyReport.of(compilation).modules().get(0).behaviors()) {
            each.partition().notRead().forEach(one -> said.add(one.at() + " " + one.reason()));
        }
        return said.stream().sorted().toList();
    }

    private static String leastOf(String value) {
        return """
                behavior f : (nums: List<Num>, bonus: Int) -> Report
                let f (nums, bonus) = {
                    let since: Map<String, Int> = List.fold(
                        (acc, p) -> Map.updateOrInsert(p.key, %s, seen -> Int.min(seen, %s), acc),
                        Map.empty, nums)
                    Report { stale = Map.keys(Map.filterEntries((k, v) -> v >= 30, since)) }
                }
                """.formatted(value, value);
    }

    @Test
    void theLeastOfEachKeyIsTheLeastOfWhatTheElementsComeToWithTheNumberBesideAddedOnce() {
        assertEquals(List.of("bonus RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE",
                        "least(nums[*].n by key) RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE"),
                notRead(leastOf("p.n + bonus")));
    }

    /** Taken away, the number beside is the same number the other way round, and the element is
     *  what it comes to taken away from nought. */
    @Test
    void theNumberBesideIsPutBackWhicheverWayTheElementIsWeighed() {
        assertEquals(List.of("bonus RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE",
                        "least({-1·n + 0 | nums[*]} by key) RELATION_NOT_SHOWN_TO_REACH_EVERY_VALUE"),
                notRead(leastOf("bonus - p.n")));
    }

    /** With nothing beside, the end of each key is read as it was. */
    @Test
    void withNothingBesideTheEndIsTheEndOfThePlace() {
        assertEquals(List.of("least(nums[*].n by key) RULE_ABOUT_A_RUN"),
                notRead(leastOf("p.n")));
    }

    /**
     * A number added for some elements and not others stands beside none of them alike, and a
     * total adds it once for each element, which is how many there are times it: neither is read.
     */
    @Test
    void aNumberAddedForSomeElementsOrAddedUpOverAllOfThemIsNotRead() {
        assertEquals(List.of("nums[*] RULE_ABOUT_A_DERIVED_VALUE"),
                notRead(leastOf("if p.flag then p.n + bonus else p.n")));
        assertEquals(List.of("nums[*] RULE_ABOUT_A_DERIVED_VALUE"), notRead("""
                behavior f : (nums: List<Num>, bonus: Int) -> Report
                let f (nums, bonus) = {
                    let since: Map<String, Int> = List.fold(
                        (acc, p) -> Map.updateOrInsert(p.key, p.n + bonus,
                                                       seen -> seen + (p.n + bonus), acc),
                        Map.empty, nums)
                    Report { stale = Map.keys(Map.filterEntries((k, v) -> v >= 30, since)) }
                }
                """));
        assertEquals(List.of("bonus RULE_ABOUT_A_DERIVED_VALUE", "nums RULE_ABOUT_A_DERIVED_VALUE",
                "nums[*].n RULE_ABOUT_A_DERIVED_VALUE"), notRead("""
                behavior f : (nums: List<Num>, bonus: Int) -> Bool
                let f (nums, bonus) = List.sum(List.map(p -> p.n + bonus, nums)) >= 30
                """));
    }

    private static String totalOf(String first, String moved) {
        return """
                behavior f : (nums: List<Num>, bonus: Int) -> Report
                let f (nums, bonus) = {
                    let since: Map<String, Int> = List.fold(
                        (acc, p) -> Map.updateOrInsert(p.key, %s, seen -> %s, acc),
                        Map.empty, nums)
                    Report { stale = Map.keys(Map.filterEntries((k, v) -> v >= 30, since)) }
                }
                """.formatted(first, moved);
    }

    /**
     * A total of each key adds what the element files first, however the sum it adds is grouped
     * and in whichever order it is written: each way is one total, read alike.
     */
    @Test
    void howTheSumATotalAddsIsGroupedSaysNothingOfWhetherItIsATotal() {
        List<String> read = notRead(totalOf("p.n + p.m", "seen + (p.n + p.m)"));
        assertEquals(List.of("total({1·m + 1·n + 0 | nums[*]} by key) RULE_ABOUT_A_RUN"), read);
        for (String moved : List.of("seen + p.n + p.m", "p.n + seen + p.m", "p.m + (p.n + seen)",
                "Int.add(seen, p.n + p.m)")) {
            assertEquals(read, notRead(totalOf("p.n + p.m", moved)), moved);
        }
        // And with a number beside each element, every way is a total of how many there are
        // times it, which is not read.
        for (String moved : List.of("seen + (p.n + bonus)", "seen + p.n + bonus")) {
            assertEquals(List.of("nums[*] RULE_ABOUT_A_DERIVED_VALUE"),
                    notRead(totalOf("p.n + bonus", moved)), moved);
        }
    }

    /** A step that adds something other than what the element files first is no total. */
    @Test
    void aStepAddingAnotherSumThanTheOneFiledFirstIsNoTotal() {
        assertEquals(List.of("nums[*] RULE_ABOUT_A_DERIVED_VALUE"),
                notRead(totalOf("p.n + p.m", "seen + p.n + p.n")));
        assertEquals(List.of("nums[*] RULE_ABOUT_A_DERIVED_VALUE"),
                notRead(totalOf("p.n + p.m", "seen + seen + p.n + p.m")));
    }

    /** The language computes the least of each key with the number beside added once. */
    @Test
    void theLanguageComputesWhatTheReadingSays() {
        Compilation compilation = Compilation.ofSource(HEAD + """
                behavior least : (nums: List<Num>, bonus: Int) -> Int
                let least (nums, bonus) = {
                    let since: Map<String, Int> = List.fold(
                        (acc, p) -> Map.updateOrInsert(p.key, p.n + bonus,
                                                       seen -> Int.min(seen, p.n + bonus), acc),
                        Map.empty, nums)
                    Map.get("a", since) |> Option.withDefault(0 - 1)
                }

                example least
                    | "one element" : ([Num { key = "a", n = 5, m = 0, flag = true }], 10) -> 15
                    | "the least of two" : ([Num { key = "a", n = 5, m = 0, flag = true },
                                             Num { key = "a", n = 3, m = 0, flag = false }],
                                            10) -> 13
                    | "another key apart" : ([Num { key = "b", n = 1, m = 0, flag = true },
                                              Num { key = "a", n = 7, m = 0, flag = false }],
                                             10) -> 17
                    | "a negative number beside" : ([Num { key = "a", n = 5, m = 0, flag = true },
                                                     Num { key = "a", n = 9, m = 0, flag = true }],
                                                    0 - 4) -> 1
                """, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();

        assertEquals(List.of(), compilation.errors().stream()
                .map(each -> each.diagnostic().code() + " " + each.diagnostic().said()).toList());
    }
}
