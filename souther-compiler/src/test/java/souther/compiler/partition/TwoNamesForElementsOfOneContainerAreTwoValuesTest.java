package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.BiPredicate;
import java.util.function.Predicate;
import java.util.stream.Collectors;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Two names for elements of one container are two values: what is asked of one is never composed
 * with what is asked of the other as though it were asked of one element.
 *
 * <p>Held against the statements themselves. Each shape is a body over the elements of
 * {@code x.items}, each element a number {@code n}, a truth {@code paid} and a case {@code tier},
 * where two closures or a closure and a quantifier hand out an element each, {@code a} and
 * {@code b}, and conditions on either stand on the way to a comparison. Whether a run gets to that
 * comparison is worked out by running the conditions over every pair of element values the
 * conditions tell apart: a container holding those two elements hands out each to each name. A
 * comparison some run gets to is never one this compiler says has no line, and one asked of the
 * row beside the elements keeps what the row is asked. Where every condition is of one name and
 * no value meets them, the comparison past them is one no row arrives at, and that is said.
 */
class TwoNamesForElementsOfOneContainerAreTwoValuesTest {

    /** The values of one element the conditions tell apart. */
    private record Value(int n, boolean paid) {}

    private static final List<Value> VALUES = values();

    private static List<Value> values() {
        List<Value> out = new ArrayList<>();
        for (int n : List.of(-1, 0, 1)) {
            for (boolean paid : List.of(false, true)) {
                out.add(new Value(n, paid));
            }
        }
        return List.copyOf(out);
    }

    /** A condition on the element {@code name} stands for, written and held. */
    private record Asked(String name, String written, Predicate<Value> holds) {

        String of() {
            return written.formatted(name);
        }

        @Override
        public String toString() {
            return of();
        }
    }

    /** What is asked of one element: a bound on its number either way, or its truth. */
    private static List<Asked> askedOf(String name) {
        return List.of(
                new Asked(name, "%s.n < 0", value -> value.n() < 0),
                new Asked(name, "%s.n >= 1", value -> value.n() >= 1),
                new Asked(name, "%s.n >= 0", value -> value.n() >= 0),
                new Asked(name, "%s.paid", Value::paid),
                new Asked(name, "Bool.not(%s.paid)", value -> !value.paid()));
    }

    private static Asked below(String name) {
        return askedOf(name).get(0);
    }

    private static Asked above(String name) {
        return askedOf(name).get(1);
    }

    private static Asked atLeastNought(String name) {
        return askedOf(name).get(2);
    }

    private static Asked paid(String name) {
        return askedOf(name).get(3);
    }

    private static Asked unpaid(String name) {
        return askedOf(name).get(4);
    }

    /**
     * The pairs what is claimed turns on: a bound on the number asked both ways and a truth asked
     * both ways, each of one name, which no value meets, and of two names, which two values do —
     * either name first; two bounds one value meets; a bound beside a truth.
     */
    private static final List<List<Asked>> PAIRS = List.of(
            List.of(below("a"), above("a")),
            List.of(paid("a"), unpaid("a")),
            List.of(below("a"), above("b")),
            List.of(below("b"), above("a")),
            List.of(paid("a"), unpaid("b")),
            List.of(above("a"), atLeastNought("a")),
            List.of(below("a"), paid("b")));

    /** Whether some value of {@code a} and some of {@code b} meet every one of {@code asked}. */
    private static boolean met(List<Asked> asked) {
        for (Value a : VALUES) {
            for (Value b : VALUES) {
                if (asked.stream().allMatch(each ->
                        each.holds().test(each.name().equals("a") ? a : b))) {
                    return true;
                }
            }
        }
        return false;
    }

    /** Whether every one of {@code asked} is of one name. */
    private static boolean ofOneName(List<Asked> asked) {
        return asked.stream().map(Asked::name).distinct().count() == 1;
    }

    private static final String DECLARED = """
            data Tier = Gold | Plain
            data Item = { n: Int, paid: Bool, tier: Tier }
                invariant n >= -10 && n <= 10
            data Input = { items: List<Item>, gate: Int }
                invariant gate >= -10 && gate <= 10

            let below (v: Item): Bool = v.n < 0
            """;

    /**
     * {@code bodies}, each the body of a behavior of its own, measured in one module: for each,
     * the positions it was said to hold a rule of without a line at.
     */
    private static Map<String, Set<String>> withoutALine(List<String> bodies) {
        StringBuilder source = new StringBuilder("module probe.twonames\n\n").append(DECLARED);
        for (int i = 0; i < bodies.size(); i++) {
            source.append("""

                    behavior f%d : (x: Input) -> Int
                    let f%d (x) = %s
                    """.formatted(i, i, bodies.get(i)));
        }
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
        for (int i = 0; i < bodies.size(); i++) {
            assertTrue(out.containsKey("f" + i), "f" + i + " was measured");
        }
        return out;
    }

    /** Where the comparison on the gate is said to have no line, against where a run gets to it. */
    private static void heldToTheRuns(List<String> bodies, List<List<Asked>> asked) {
        Map<String, Set<String>> without = withoutALine(bodies);
        List<String> wrong = new ArrayList<>();
        int closed = 0;
        for (int i = 0; i < bodies.size(); i++) {
            boolean noLine = without.get("f" + i).contains("x.gate");
            List<Asked> each = asked.get(i);
            if (met(each) && noLine) {
                wrong.add("some run gets to the gate past " + each + ": " + bodies.get(i));
            }
            if (!met(each) && ofOneName(each)) {
                closed++;
                if (!noLine) {
                    wrong.add("no run gets to the gate past " + each + ": " + bodies.get(i));
                }
            }
        }
        assertTrue(closed > 0, "some shape asks one name what no value meets");
        assertEquals(List.of(), wrong, "the gate's line against the runs");
    }

    /** Two conditions joined on the way, each read through the closure that hands its name out. */
    @Test
    void twoConditionsJoinedInsideTwoClosuresAreOfTheirOwnElements() {
        List<String> bodies = new ArrayList<>();
        List<List<Asked>> asked = PAIRS;
        for (List<Asked> two : asked) {
            bodies.add(("List.sum(List.map(a -> List.sum(List.map(b -> if %s && %s && x.gate > 0"
                    + " then 1 else 0, x.items)), x.items))")
                    .formatted(two.getFirst().of(), two.getLast().of()));
        }
        heldToTheRuns(bodies, asked);
    }

    /** Two conditions joined by a connective, written and held of the two elements' values. */
    private record Joined(String written, BiPredicate<Boolean, Boolean> holds) {}

    /**
     * The two joined every way a denial and a disjunction can join them: a way past such a
     * condition is one of several, or the denial of a conjunction, and what is left out of a way
     * of several may never narrow the others.
     */
    @Test
    void twoConditionsJoinedByADisjunctionOrADenialAreOfTheirOwnElements() {
        List<Joined> joins = List.of(
                new Joined("%s || %s", (p, q) -> p || q),
                new Joined("Bool.not(%s && %s)", (p, q) -> !(p && q)),
                new Joined("Bool.not(%s) && %s", (p, q) -> !p && q),
                new Joined("Bool.not(%s || %s)", (p, q) -> !p && !q));
        List<String> bodies = new ArrayList<>();
        List<List<Asked>> asked = new ArrayList<>();
        List<Joined> joinedBy = new ArrayList<>();
        for (Joined join : joins) {
            for (List<Asked> two : PAIRS) {
                bodies.add(("List.sum(List.map(a -> List.sum(List.map(b -> if %s then (if x.gate"
                        + " > 0 then 1 else 2) else 3, x.items)), x.items))").formatted(
                        join.written().formatted(two.getFirst().of(), two.getLast().of())));
                asked.add(two);
                joinedBy.add(join);
            }
        }
        Map<String, Set<String>> without = withoutALine(bodies);
        List<String> wrong = new ArrayList<>();
        for (int i = 0; i < bodies.size(); i++) {
            List<Asked> two = asked.get(i);
            Joined join = joinedBy.get(i);
            boolean met = false;
            for (Value a : VALUES) {
                for (Value b : VALUES) {
                    Value first = two.getFirst().name().equals("a") ? a : b;
                    Value second = two.getLast().name().equals("a") ? a : b;
                    met |= join.holds().test(two.getFirst().holds().test(first),
                            two.getLast().holds().test(second));
                }
            }
            boolean noLine = without.get("f" + i).contains("x.gate");
            if (met && noLine) {
                wrong.add("some run gets to the gate past: " + bodies.get(i));
            }
        }
        assertEquals(List.of(), wrong, "the gate's line against the runs");
    }

    /**
     * A helper's parameter read at two calls is two values, one for each element it was handed,
     * and at one call it is one: the helper asked of {@code a} and denied of {@code b} is met by
     * two elements, and asked and denied of {@code a} by none.
     */
    @Test
    void aHelpersParameterAtTwoCallsIsTwoValuesAndAtOneCallOne() {
        Map<String, Set<String>> without = withoutALine(List.of(
                "List.sum(List.map(a -> List.sum(List.map(b -> if below(a) && Bool.not(below(b))"
                        + " && x.gate > 0 then 1 else 0, x.items)), x.items))",
                "List.sum(List.map(a -> List.sum(List.map(b -> if below(a) && Bool.not(below(a))"
                        + " && x.gate > 0 then 1 else 0, x.items)), x.items))"));
        assertEquals(List.of(false, true), List.of(without.get("f0").contains("x.gate"),
                without.get("f1").contains("x.gate")),
                "the gate past two elements is reached, and past one asked both ways is not");
    }

    /**
     * One closure value applied to two elements is two values, and applied to one element twice
     * is one: the same function asked of {@code a} and denied of {@code b} is met by two elements,
     * and asked and denied of {@code a} by none.
     */
    @Test
    void oneClosureAppliedToTwoElementsIsTwoValuesAndToOneOne() {
        String body = """
                {
                        let p = (v) -> v.n < 0
                        List.sum(List.map(a -> List.sum(List.map(b -> if p(a) && Bool.not(p(%s))\
                 && x.gate > 0 then 1 else 0, x.items)), x.items))
                    }""";
        Map<String, Set<String>> without = withoutALine(List.of(body.formatted("b"),
                body.formatted("a")));
        assertEquals(List.of(false, true), List.of(without.get("f0").contains("x.gate"),
                without.get("f1").contains("x.gate")),
                "the gate past two elements is reached, and past one asked both ways is not");
    }

    /**
     * A name given only another name is that name's element: what is asked through {@code c},
     * bound to {@code a}, is asked of {@code a}'s element, and of {@code b}'s never.
     */
    @Test
    void aNameGivenAnotherIsThatNamesElement() {
        String body = """
                List.sum(List.map(a -> List.sum(List.map(b -> {
                            let c = a
                            if %s && %s && x.gate > 0 then 1 else 0
                        }, x.items)), x.items))""";
        List<String> bodies = new ArrayList<>();
        List<List<Asked>> asked = new ArrayList<>();
        for (List<Asked> two : PAIRS) {
            Asked first = two.getFirst();
            if (first.name().equals("a")) {
                bodies.add(body.formatted(first.written().formatted("c"), two.getLast().of()));
                asked.add(two);
            }
        }
        heldToTheRuns(bodies, asked);
    }

    /**
     * A quantifier reading its own element twice reads one value: what one element meets is
     * reached, and bounds on its number no value meets hold of none, so the gate past them is
     * reached by no run.
     *
     * <p>A truth asked and denied of the element is met by no element either, and is not asked
     * to close here: a quantifier's body is not refuted by its truths, which says nothing of which
     * value they are about.
     */
    @Test
    void aQuantifierReadingItsElementTwiceReadsOneValue() {
        List<String> bodies = new ArrayList<>();
        List<List<Asked>> asked = PAIRS.stream()
                .filter(two -> ofOneName(two) && two.getFirst().name().equals("a")).toList();
        for (List<Asked> two : asked) {
            bodies.add("if List.any(a -> %s && %s, x.items) && x.gate > 0 then 1 else 0"
                    .formatted(two.getFirst().of(), two.getLast().of()));
        }
        Map<String, Set<String>> without = withoutALine(bodies);
        List<String> wrong = new ArrayList<>();
        int closed = 0;
        for (int i = 0; i < bodies.size(); i++) {
            boolean noLine = without.get("f" + i).contains("x.gate");
            List<Asked> two = asked.get(i);
            boolean ofNumbers = two.stream().allMatch(each -> each.written().contains(".n "));
            if (met(two) && noLine) {
                wrong.add("some run gets to the gate past " + two);
            }
            if (!met(two) && ofNumbers) {
                closed++;
                if (!noLine) {
                    wrong.add("no run gets to the gate past " + two);
                }
            }
        }
        assertTrue(closed > 0, "some shape asks the element what no value meets");
        assertEquals(List.of(), wrong, "the gate's line against the runs");
    }

    /**
     * Two quantifiers over one container each own their element, under one name or two: what one
     * asks of its element and the other of its own are asked of two elements, each of which some
     * value meets, so the gate past both is reached.
     */
    @Test
    void twoQuantifiersEachOwnTheirElementWhateverTheyCallIt() {
        List<String> bodies = new ArrayList<>();
        // What no one value meets, asked of each quantifier's own: a bound either way, a truth
        // either way.
        for (String second : List.of("a", "b")) {
            for (Asked first : List.of(below("a"), paid("a"))) {
                for (Asked other : List.of(above(second), unpaid(second))) {
                    bodies.add(("if List.any(a -> %s, x.items) && List.any(%s -> %s, x.items)"
                            + " && x.gate > 0 then 1 else 0").formatted(first.of(), second,
                            other.of()));
                }
            }
        }
        Map<String, Set<String>> without = withoutALine(bodies);
        List<String> wrong = new ArrayList<>();
        for (int i = 0; i < bodies.size(); i++) {
            if (without.get("f" + i).contains("x.gate")) {
                wrong.add(bodies.get(i));
            }
        }
        assertEquals(List.of(), wrong, "some run gets to the gate past each of these");
    }

    /** The same two met as two forks one inside the other, which put them on the way apart. */
    @Test
    void twoForksOneInsideTheOtherAreOfTheirOwnElements() {
        List<String> bodies = new ArrayList<>();
        List<List<Asked>> asked = PAIRS;
        for (List<Asked> two : asked) {
            bodies.add(("List.sum(List.map(a -> List.sum(List.map(b -> if %s then (if %s then"
                    + " (if x.gate > 0 then 1 else 2) else 3) else 4, x.items)), x.items))")
                    .formatted(two.getFirst().of(), two.getLast().of()));
        }
        heldToTheRuns(bodies, asked);
    }

    /**
     * A name a closure hands out, read inside a quantifier over the same container beside the
     * quantifier's own element: the two are two elements, which the quantifier's element is not.
     */
    @Test
    void aNameReadInsideAQuantifierOverItsContainerIsNotTheQuantifiersElement() {
        List<String> bodies = new ArrayList<>();
        List<List<Asked>> asked = new ArrayList<>();
        for (List<Asked> two : PAIRS) {
            if (!two.getFirst().name().equals("a") || !two.getLast().name().equals("b")) {
                continue;
            }
            bodies.add(("List.sum(List.map(a -> if List.any(b -> %s && %s, x.items)"
                    + " && x.gate > 0 then 1 else 0, x.items))")
                    .formatted(two.getLast().of(), two.getFirst().of()));
            asked.add(two);
        }
        Map<String, Set<String>> without = withoutALine(bodies);
        List<String> wrong = new ArrayList<>();
        for (int i = 0; i < bodies.size(); i++) {
            if (met(asked.get(i)) && without.get("f" + i).contains("x.gate")) {
                wrong.add(bodies.get(i));
            }
        }
        assertEquals(List.of(), wrong, "some run gets to the gate past each of these");
    }

    /**
     * A comparison of one name's element past a condition on the other's draws its line: what the
     * way asks of the other element says nothing of the values this one takes.
     */
    @Test
    void aLineOnOneNamePastAConditionOnTheOtherIsDrawn() {
        List<String> bodies = new ArrayList<>();
        for (Asked first : askedOf("a")) {
            bodies.add(("List.sum(List.map(a -> if %s then List.sum(List.map(b ->"
                    + " if b.n > 0 then 1 else 0, x.items)) else 0, x.items))")
                    .formatted(first.of()));
        }
        Map<String, Set<String>> without = withoutALine(bodies);
        List<String> wrong = new ArrayList<>();
        for (int i = 0; i < bodies.size(); i++) {
            if (!without.get("f" + i).isEmpty()) {
                wrong.add(bodies.get(i) + " " + without.get("f" + i));
            }
        }
        assertEquals(List.of(), wrong, "every comparison here draws its line");
    }

    /**
     * A condition on the row beside conditions on two elements is still taken in: the gate past
     * {@code x.gate > 5} is decided by it, whatever is asked of the elements.
     */
    @Test
    void aConditionOnTheRowBesideTwoElementsIsStillTakenIn() {
        List<String> bodies = new ArrayList<>();
        for (Asked first : List.of(below("a"), paid("a"))) {
            for (Asked second : List.of(above("b"), unpaid("b"))) {
                bodies.add(("List.sum(List.map(a -> List.sum(List.map(b -> if %s && %s"
                        + " && x.gate > 5 then (if x.gate > 0 then 1 else 2) else 3, x.items)),"
                        + " x.items))").formatted(first.of(), second.of()));
            }
        }
        Map<String, Set<String>> without = withoutALine(bodies);
        List<String> wrong = new ArrayList<>();
        for (int i = 0; i < bodies.size(); i++) {
            if (!without.get("f" + i).contains("x.gate")) {
                wrong.add(bodies.get(i));
            }
        }
        assertEquals(List.of(), wrong, "the way decides the gate past each of these");
    }

    /**
     * Cases: an arm entered on the case of one name and an arm inside it on the case of another
     * are two elements' cases; on one name's, two cases are none.
     */
    @Test
    void theCasesOfTwoNamesAreTheCasesOfTwoElements() {
        List<String> bodies = new ArrayList<>();
        List<Boolean> reached = new ArrayList<>();
        List<Boolean> oneName = new ArrayList<>();
        for (String outer : List.of("a", "b")) {
            for (String inner : List.of("a", "b")) {
                for (String first : List.of("Gold", "Plain")) {
                    for (String second : List.of("Gold", "Plain")) {
                        String otherFirst = first.equals("Gold") ? "Plain" : "Gold";
                        String otherSecond = second.equals("Gold") ? "Plain" : "Gold";
                        bodies.add(("List.sum(List.map(a -> List.sum(List.map(b ->"
                                + " match %s.tier with | %s -> (match %s.tier with"
                                + " | %s -> (if x.gate > 0 then 1 else 2) | %s -> 3)"
                                + " | %s -> 4, x.items)), x.items))").formatted(outer, first,
                                inner, second, otherSecond, otherFirst));
                        reached.add(!outer.equals(inner) || first.equals(second));
                        oneName.add(outer.equals(inner));
                    }
                }
            }
        }
        Map<String, Set<String>> without = withoutALine(bodies);
        List<String> wrong = new ArrayList<>();
        for (int i = 0; i < bodies.size(); i++) {
            boolean noLine = without.get("f" + i).contains("x.gate");
            if (reached.get(i) == noLine && (reached.get(i) || oneName.get(i))) {
                wrong.add((reached.get(i) ? "reached: " : "not reached: ") + bodies.get(i));
            }
        }
        assertEquals(List.of(), wrong, "the gate's line against the runs");
    }
}
