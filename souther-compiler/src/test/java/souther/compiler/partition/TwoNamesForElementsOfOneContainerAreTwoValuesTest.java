package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Two names for elements of one container are two values, however the names were written: what
 * is asked of one is never composed with what is asked of the other as though it were asked of one
 * element, and what one name is asked twice is asked of one element.
 *
 * <p>Held where it shows, at the comparison past them. Each body hands out elements of
 * {@code x.items} through a way of writing a name, asks a bound of each, and compares the row's
 * {@code x.gate} past them. Asked of two names, two elements meet the bounds and some run gets to
 * the comparison, which then has a line; asked of one, no element meets them and no run gets there,
 * which is said. How a statement is told its names and which conditions a way holds are asked of
 * their own readers ({@code WhatANameStoodForIsTheValueAPartIsAboutTest},
 * {@link AWayHoldsOneElementOfAContainerTest}); this asks only that each way of writing a name
 * reaches them.
 */
class TwoNamesForElementsOfOneContainerAreTwoValuesTest {

    private static final String DECLARED = """
            data Tier = Gold | Plain
            data Item = { n: Int, tier: Tier }
                invariant n >= -10 && n <= 10
            data Input = { items: List<Item>, gate: Int }
                invariant gate >= -10 && gate <= 10

            let below (v: Item): Bool = v.n < 0
            """;

    /** Over two closures, {@code a} outside and {@code b} inside, with {@code %s} what is asked
     *  past both. */
    private static String inTwoClosures(String asked) {
        return "List.sum(List.map(a -> List.sum(List.map(b -> " + asked + ", x.items)), x.items))";
    }

    /** Each body by its name, in the one module this compiles. */
    private static final Map<String, String> BODIES = bodies();

    private static Map<String, String> bodies() {
        Map<String, String> out = new LinkedHashMap<>();
        for (String other : List.of("b", "a")) {
            String apart = other.equals("b") ? "Apart" : "Alike";
            out.put("joined" + apart, inTwoClosures(
                    "if a.n < 0 && %s.n >= 1 && x.gate > 0 then 1 else 0".formatted(other)));
            out.put("forks" + apart, inTwoClosures(("if a.n < 0 then (if %s.n >= 1 then"
                    + " (if x.gate > 0 then 1 else 2) else 3) else 4").formatted(other)));
            out.put("helper" + apart, inTwoClosures(
                    "if below(a) && Bool.not(below(%s)) && x.gate > 0 then 1 else 0"
                            .formatted(other)));
            out.put("closureValue" + apart, """
                    {
                            let p = (v) -> v.n < 0
                            %s
                        }""".formatted(inTwoClosures(
                    "if p(a) && Bool.not(p(%s)) && x.gate > 0 then 1 else 0".formatted(other))));
            out.put("alias" + apart, """
                    List.sum(List.map(a -> List.sum(List.map(b -> {
                                let c = a
                                if c.n < 0 && %s.n >= 1 && x.gate > 0 then 1 else 0
                            }, x.items)), x.items))""".formatted(other));
            out.put("cases" + apart, inTwoClosures(("match a.tier with | Gold -> (match %s.tier"
                    + " with | Plain -> (if x.gate > 0 then 1 else 2) | Gold -> 3)"
                    + " | Plain -> 4").formatted(other)));
        }
        // A denial of a disjunction, which is a way past both: a.n < 0 and b.n >= 0.
        out.put("deniedDisjunction", inTwoClosures(
                "if Bool.not(a.n >= 0 || b.n < 0) then (if x.gate > 0 then 1 else 2) else 3"));
        // A quantifier's own element asked twice is one element, and two quantifiers' are two
        // whatever each calls its own.
        out.put("quantifierAlike",
                "if List.any(a -> a.n < 0 && a.n >= 1, x.items) && x.gate > 0 then 1 else 0");
        out.put("twoQuantifiers", "if List.any(a -> a.n < 0, x.items)"
                + " && List.any(a -> a.n >= 1, x.items) && x.gate > 0 then 1 else 0");
        // A name a closure hands out, read inside a quantifier over the same container, is not the
        // quantifier's element.
        out.put("insideAQuantifier", "List.sum(List.map(a -> if List.any(b -> b.n >= 1"
                + " && a.n < 0, x.items) && x.gate > 0 then 1 else 0, x.items))");
        return out;
    }

    /** For each body, the positions it was said to hold a rule of without a line at. */
    private static final Map<String, Set<String>> WITHOUT_A_LINE = withoutALine();

    private static Map<String, Set<String>> withoutALine() {
        StringBuilder source = new StringBuilder("module probe.twonames\n\n").append(DECLARED);
        BODIES.forEach((name, body) -> source.append("""

                behavior %s : (x: Input) -> Int
                let %s (x) = %s
                """.formatted(name, name, body)));
        Compilation made = Compilation.ofSource(source.toString(), "Main");
        assertEquals(List.of(), made.errors().stream()
                .map(each -> each.diagnostic().code()).toList(), "the model compiles");
        made.measure(Adequacy.Asked.fullReport());
        made.answerEverything();
        Map<String, Set<String>> out = new LinkedHashMap<>();
        AdequacyReport.of(made).modules().getFirst().behaviors().forEach(behavior ->
                out.put(behavior.name(), behavior.partition().notRead().stream()
                        .filter(PartitionEvidence.NotRead.ARule.class::isInstance)
                        .map(PartitionEvidence.NotRead::at)
                        .collect(Collectors.toUnmodifiableSet())));
        assertEquals(BODIES.keySet(), out.keySet(), "every body was measured");
        return out;
    }

    /** Whether the comparison on the gate was said to have no line in each of {@code bodies}. */
    private static Map<String, Boolean> noLineAtTheGate(String... bodies) {
        Map<String, Boolean> out = new LinkedHashMap<>();
        for (String each : bodies) {
            out.put(each, WITHOUT_A_LINE.get(each).contains("x.gate"));
        }
        return out;
    }

    /**
     * Through each way of writing a name — a closure, a fork inside it, a helper's parameter, a
     * function value applied, a name given another, an arm of a case — two names are two elements
     * and the gate past them is reached, and one name asked both ways is one element and is not.
     */
    @Test
    void eachWayOfWritingANameIsTheElementItWasHanded() {
        Map<String, Boolean> expected = new LinkedHashMap<>();
        for (String shape : List.of("joined", "forks", "helper", "closureValue", "alias",
                "cases")) {
            expected.put(shape + "Apart", false);
            expected.put(shape + "Alike", true);
        }
        assertEquals(expected, noLineAtTheGate(expected.keySet().toArray(String[]::new)));
    }

    /** A denial of a disjunction is a way past both of its parts, each of its own element. */
    @Test
    void aDeniedDisjunctionOfTwoNamesIsAWayPastTwoElements() {
        assertEquals(Map.of("deniedDisjunction", false), noLineAtTheGate("deniedDisjunction"));
    }

    /**
     * A quantifier's element is its own: asked twice inside one quantifier it is one element,
     * inside two it is two, and beside a name for another element it is not that element.
     */
    @Test
    void aQuantifierOwnsItsElement() {
        assertEquals(Map.of("quantifierAlike", true, "twoQuantifiers", false,
                        "insideAQuantifier", false),
                noLineAtTheGate("quantifierAlike", "twoQuantifiers", "insideAQuantifier"));
    }
}
