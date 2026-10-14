package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.partition.DecisionReading;
import souther.compiler.partition.OnTheWay;
import souther.compiler.partition.RuleStep;
import souther.compiler.types.ExpansionLineage;
import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a way of a rule asks of a row is told the calls of a helper each part of it was read off,
 * and no call a part was not read off.
 *
 * <p>The body calls the helper three times, and each call compares what the call before it handed
 * on. So the second call's comparison asks what the first call's fork decided beside what it
 * compares itself: one condition of the way, read off two calls. Told by the condition it ended up
 * under, a part read off the first call's fork would be sent to the second call — and an equal
 * part the first call asks itself would be told the second call too.
 */
class WhatAWayAsksIsReadOffTheCallsItCameFromTest {

    private static final String TAKE = """
            module example.draw

            data MB = Int
                invariant value >= 0
            data Held = { carried: MB, plan: MB, extra: MB }
            data Drawn = { fromCarried: MB, fromPlan: MB, fromExtra: MB, throttled: MB }

            behavior draw : (used: MB, held: Held) -> Drawn
                constructs Drawn, MB

            let draw (used, held) = {
                let (a, rest1) = take(used, held.carried)
                let (b, rest2) = take(rest1, held.plan)
                let (c, rest3) = take(rest2, held.extra)
                Drawn { fromCarried = a, fromPlan = b, fromExtra = c, throttled = rest3 }
            }

            let take (used: MB, cap: MB): (MB, MB) =
                if used.value <= cap.value then (used, MB(0))
                else (cap, MB(used.value - cap.value))
            """;

    /** The limit each call of the helper is handed, in the order the body calls it. */
    private static final List<String> LIMITS = List.of("held.carried", "held.plan", "held.extra");

    /**
     * Each part is read off the call whose limit it weighs, which is the latest of the calls it
     * turns on: a call weighs its own limit against what every call before it left.
     */
    @Test
    void eachPartIsReadOffTheCallWhoseLimitItWeighs() {
        int readThrough = 0;
        int parts = 0;
        for (DecisionReading.Ruled rule : found(TAKE, "draw")) {
            List<ModelOccurrence> calls = new ArrayList<>();
            for (RuleStep step : rule.steps()) {
                calls.add(step.shown().copy().orElseThrow());
            }
            assertEquals(LIMITS.size(), Set.copyOf(calls).size(),
                    () -> "each step is seen at one call of the helper: " + calls);
            for (RuleStep step : rule.steps()) {
                for (OnTheWay.TakenIn each : takenIn(step.states())) {
                    ModelOccurrence expected = calls.get(latestLimit(each));
                    assertEquals(List.of(expected), step.said().entries().get(each),
                            () -> "read off the call whose limit it weighs: " + each);
                    parts++;
                    if (!expected.equals(step.shown().copy().orElseThrow())) {
                        readThrough++;
                    }
                }
            }
        }
        assertTrue(parts > 0, "the ways ask something of a row");
        assertTrue(readThrough > 0, "and some part of a way is read off a call other than the one"
                + " its step is seen at, which is what tells the parts' calls from the step's");
    }

    /** One of several things is read off what each of them was, and nothing else. */
    @Test
    void oneOfSeveralThingsIsReadOffWhatEachOfThemWas() {
        int checked = 0;
        for (DecisionReading.Ruled rule : found(TAKE, "draw")) {
            for (RuleStep step : rule.steps()) {
                for (OnTheWay.OneOf each : oneOf(step.states())) {
                    Set<ModelOccurrence> alternatives = new LinkedHashSet<>();
                    each.alternatives().forEach(alternative -> alternative.forEach(one ->
                            alternatives.addAll(step.said().entries().getOrDefault(one,
                                    List.of()))));
                    List<ModelOccurrence> told = step.said().entries().get(each);
                    assertNotNull(told, () -> "one of several things is read off something");
                    assertEquals(alternatives, Set.copyOf(told),
                            () -> "read off what its alternatives were: " + each);
                    checked++;
                }
            }
        }
        assertTrue(checked > 0, "a way of the body asks one of several things");
    }

    private static final String JOINED = """
            module example.joined

            data Line = { a: Int, b: Int }

            behavior f : (xs: List<Line>, ys: List<Line>, n: Int) -> Int

            let ok (zs: List<Line>): Bool =
                List.sum(List.map(x -> x.a, zs)) + List.sum(List.map(x -> x.b, zs)) > 0

            let f (xs, ys, n) =
                if ok(xs) && ok(ys) then 1 else (if n < 10 then 2 else 3)
            """;

    /**
     * The halves of a joined condition stand in two calls, and each part is read off its half's
     * call — the same call whichever way the condition came out — and a condition written in the
     * body itself is read off the body, which no call made.
     */
    @Test
    void eachHalfOfAJoinedConditionIsReadOffItsOwnCall() {
        Map<String, Set<List<ModelOccurrence>>> byList = Map.of("xs", new LinkedHashSet<>(),
                "ys", new LinkedHashSet<>(), "n", new LinkedHashSet<>());
        for (DecisionReading.Ruled rule : found(JOINED, "f")) {
            for (RuleStep step : rule.steps()) {
                for (OnTheWay.TakenIn each : takenIn(step.states())) {
                    String about = each.demand().terms().stream().map(NumericTerm::toString)
                            .map(term -> term.contains("xs") ? "xs"
                                    : term.contains("ys") ? "ys" : "n")
                            .distinct().reduce((one, other) -> one + other).orElseThrow();
                    byList.get(about).add(step.said().entries().getOrDefault(each, List.of()));
                }
            }
        }
        for (String half : List.of("xs", "ys")) {
            assertEquals(1, byList.get(half).size(),
                    () -> "the half over " + half + " is read off one call: " + byList);
            assertEquals(1, byList.get(half).iterator().next().size(),
                    () -> "and only that one: " + byList);
        }
        assertNotEquals(byList.get("xs"), byList.get("ys"), "and the two halves' calls are two");
        assertEquals(1, byList.get("n").size(), () -> "read off one copy: " + byList);
        List<ModelOccurrence> body = byList.get("n").iterator().next();
        assertEquals(1, body.size(), () -> "a condition the body writes is read off the body: "
                + byList);
        assertEquals(ExpansionLineage.ORIGINAL, body.getFirst().lineage(),
                "which is the copy no call made");
    }

    private static final String TWICE = """
            module example.twice

            behavior f : (n: Int) -> Int

            let positive (k: Int): Bool = k > 0

            let f (n) = if positive(n) then (if positive(n) then 1 else 2) else 3
            """;

    /**
     * One condition consulted at two calls of a helper is one condition of the rule, and the rule
     * keeps both: where each was seen and what each was read off.
     */
    @Test
    void aConditionConsultedAtTwoCallsKeepsBoth() {
        boolean both = false;
        for (DecisionReading.Ruled rule : found(TWICE, "f")) {
            for (RuleStep step : rule.steps()) {
                Set<ModelOccurrence> seen = new LinkedHashSet<>();
                step.seen().forEach(place -> place.copy().ifPresent(seen::add));
                if (seen.size() == 2) {
                    assertEquals(seen, Set.copyOf(step.said().copies()),
                            "read off the two calls it was seen at");
                    both = true;
                }
            }
        }
        assertTrue(both, "the way through both calls consults the condition at both");
    }

    private static final String EITHER = """
            module example.either

            behavior f : (n: Int, m: Int) -> Int

            let positive (k: Int): Bool = k > 0

            let f (n, m) = if positive(n) || positive(n) then 1 else (if m < 10 then 2 else 3)
            """;

    /**
     * Two halves asking alike are one thing asked, read off every call the way consulted it at:
     * the halves stand in two calls, and a way past both failing went through both.
     */
    @Test
    void halvesAskingAlikeAreReadOffEveryCallTheWayConsulted() {
        boolean both = false;
        for (DecisionReading.Ruled rule : found(EITHER, "f")) {
            for (RuleStep step : rule.steps()) {
                Set<ModelOccurrence> seen = new LinkedHashSet<>();
                step.seen().forEach(place -> place.copy().ifPresent(seen::add));
                for (OnTheWay.TakenIn each : takenIn(step.states())) {
                    if (each.demand().terms().stream()
                            .anyMatch(term -> term.toString().equals("n"))) {
                        assertEquals(seen,
                                Set.copyOf(step.said().entries().getOrDefault(each, List.of())),
                                () -> "read off the calls it was consulted at: " + each);
                        both |= seen.size() == 2;
                    }
                }
            }
        }
        assertTrue(both, "and a way past both halves failing consulted both calls");
    }

    /** Which call's limit is the latest {@code part} weighs. */
    private static int latestLimit(OnTheWay.TakenIn part) {
        int latest = -1;
        for (NumericTerm term : part.demand().terms()) {
            latest = Math.max(latest, LIMITS.indexOf(term.toString()));
        }
        assertNotEquals(-1, latest, () -> "a part of the way weighs some call's limit: " + part);
        return latest;
    }

    private static List<OnTheWay.TakenIn> takenIn(List<OnTheWay> way) {
        List<OnTheWay.TakenIn> out = new ArrayList<>();
        for (OnTheWay each : way) {
            switch (each) {
                case OnTheWay.TakenIn taken -> out.add(taken);
                case OnTheWay.OneOf several ->
                        several.alternatives().forEach(one -> out.addAll(takenIn(one)));
                default -> { }
            }
        }
        return out;
    }

    private static List<OnTheWay.OneOf> oneOf(List<OnTheWay> way) {
        List<OnTheWay.OneOf> out = new ArrayList<>();
        for (OnTheWay each : way) {
            if (each instanceof OnTheWay.OneOf several) {
                out.add(several);
                several.alternatives().forEach(one -> out.addAll(oneOf(one)));
            }
        }
        return out;
    }

    private static List<DecisionReading.Ruled> found(String model, String behavior) {
        Compilation compilation = Compilation.ofSource(model, "Main");
        compilation.measure(Adequacy.Asked.fullReport());
        compilation.answerEverything();
        assertEquals(List.of(), compilation.errors().stream()
                        .map(e -> e.diagnostic().code().toString()).toList(),
                "the model under test compiles");
        String module = compilation.modules().getFirst();
        DecisionEvidence decided =
                compilation.db().ask(new Adequacy.Decides(module)).value().get(behavior);
        assertNotNull(decided, "the body states a decision");
        List<DecisionReading.Ruled> found = decided.read().found();
        assertFalse(found.isEmpty(), "the body has rules");
        return found;
    }
}
