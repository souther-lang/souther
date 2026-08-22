package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.AffineConstraint.Read;
import souther.compiler.numeric.AffineReduction.Reduction;
import souther.compiler.numeric.NumericDomain.Rel;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A rule over several positions narrows each of them, and never past what the rules admit.
 *
 * <p>The issue's own example. Under
 *
 * <pre>
 *     0 &lt;= straw &lt;= 10      0 &lt;= choco &lt;= 6      300·straw + 600·choco &lt;= 4800
 * </pre>
 *
 * <p>nothing derived that {@code choco >= 0} and the rule together leave {@code straw} at most
 * sixteen. Every measure that read a position's range read it short of what the rules stated.
 *
 * <p>Soundness is the whole of the work here, and it is the one thing argument is worst at: a bound
 * derived too tight refuses rows a model admits and nothing downstream is in a position to notice.
 * So it is checked against the points themselves, enumerated over a bounded range rather than
 * sampled, and the claim asserted is the one that matters — no point the rules admit is ever left
 * outside what this derives.
 */
class ARuleOverSeveralPositionsNarrowsEachOfThemTest {

    private static final List<String> POSITIONS = List.of("a", "b", "c");
    private static final int LOW = -4;
    private static final int HIGH = 4;
    private static final int CASES = 400;

    private record Written(Map<String, Rational> coefs, Rational constant, Rel rel) {}

    private static Rational num(long whole) {
        return Rational.of(whole);
    }

    private static Map<String, Rational> weighing(Object... pairs) {
        Map<String, Rational> out = new LinkedHashMap<>();
        for (int i = 0; i < pairs.length; i += 2) {
            out.put((String) pairs[i], num((Integer) pairs[i + 1]));
        }
        return out;
    }

    private static AffineConstraint<String> rule(Map<String, Rational> coefs, long constant,
                                                 Rel rel, Granularity spacing) {
        return assertInstanceOf(Read.Stated.class,
                AffineConstraint.of(coefs, num(constant), rel, atom -> spacing)).constraint();
    }

    private static Box<String> between(Object... triples) {
        Map<String, RationalCut> least = new LinkedHashMap<>();
        Map<String, RationalCut> most = new LinkedHashMap<>();
        for (int i = 0; i < triples.length; i += 3) {
            String atom = (String) triples[i];
            least.put(atom, RationalCut.inclusive(num((Integer) triples[i + 1])));
            most.put(atom, RationalCut.inclusive(num((Integer) triples[i + 2])));
        }
        return new Box<>(least, most);
    }

    private static Reduction.Tightened<String> reduce(List<AffineConstraint<String>> rules,
                                                      Box<String> from, Granularity spacing) {
        return assertInstanceOf(Reduction.Tightened.class,
                AffineReduction.over(reading(rules, from), atom -> spacing));
    }

    /**
     * The rules read against {@code from}, which is what a round of the closure hands the reduction —
     * or null where the differences alone already hold nothing, which is where a round is never
     * reached.
     */
    private static FormReach<String> reading(List<AffineConstraint<String>> rules, Box<String> from) {
        DifferenceBounds<String> differences = DifferenceBounds.over(rules);
        return differences.holdsNothing() ? null : FormReach.over(rules, from, differences);
    }

    // --- the issue's example -----------------------------------------------------------------------

    @Test
    void theRuleAndWhatTheOthersAreLeftBoundThePosition() {
        AffineConstraint<String> budget =
                rule(weighing("straw", 300, "choco", 600), -4800, Rel.LE, Granularity.DISCRETE);
        Box<String> from = between("straw", 0, 1000, "choco", 0, 6);

        Reduction.Tightened<String> found =
                reduce(List.of(budget), from, Granularity.DISCRETE);

        assertEquals(RationalCut.inclusive(num(16)), found.atMost().get("straw"),
                "choco is never below nought, so the rule leaves straw at most sixteen");
        assertEquals(RationalCut.inclusive(num(8)), found.atMost().get("choco"),
                "and straw is never below nought, so it leaves choco at most eight");
        assertNull(found.atLeast().get("straw"), "and says nothing below, which the rule does not");
    }

    /** What the other positions are left is read from the box, so a tighter box says more. */
    @Test
    void whatTheOthersAreLeftIsWhatTheBoxSays() {
        AffineConstraint<String> budget =
                rule(weighing("straw", 300, "choco", 600), -4800, Rel.LE, Granularity.DISCRETE);
        assertEquals(RationalCut.inclusive(num(4)),
                reduce(List.of(budget), between("straw", 0, 1000, "choco", 6, 6),
                        Granularity.DISCRETE).atMost().get("straw"),
                "with choco pinned at six the rule leaves straw at most four");
    }

    /** A position pulling the sum down contributes least at its greatest, which is the sign error
     *  that would otherwise be invisible until something reported a row nobody can build. */
    @Test
    void aPositionWeighedNegativelyIsReadFromItsOtherEnd() {
        AffineConstraint<String> rule =
                rule(weighing("a", 1, "b", -1, "c", 1), -10, Rel.LE, Granularity.DISCRETE);
        assertEquals(RationalCut.inclusive(num(14)),
                reduce(List.of(rule), between("a", 0, 100, "b", 0, 5, "c", 1, 3),
                        Granularity.DISCRETE).atMost().get("a"),
                "b is at most five and c at least one, so a is at most 10 + 5 - 1");
    }

    @Test
    void aPositionWithoutTheEndThatMattersLeavesTheRuleSayingNothing() {
        AffineConstraint<String> rule =
                rule(weighing("a", 1, "b", 1), -10, Rel.LE, Granularity.DISCRETE);
        Map<String, RationalCut> nothing = Map.of();
        Reduction.Tightened<String> found = reduce(List.of(rule),
                new Box<>(nothing, nothing), Granularity.DISCRETE);
        assertTrue(found.atLeast().isEmpty() && found.atMost().isEmpty(),
                "nothing bounds b below, so the sum bounds a at nothing");
    }

    @Test
    void aBoundReachedByNothingMakesWhatFollowsStrict() {
        AffineConstraint<String> rule =
                rule(weighing("a", 1, "b", 1), -10, Rel.LE, Granularity.DENSE);
        Box<String> from = new Box<>(Map.of("b", RationalCut.exclusive(num(2))), Map.of());
        assertEquals(RationalCut.exclusive(num(8)),
                reduce(List.of(rule), from, Granularity.DENSE).atMost().get("a"),
                "b never quite reaches two, so a never quite reaches eight");
    }

    /** Turning `k·a <= w - m` into a bound on `a` is handed back to the one place that decides it,
     *  so what it does about the values `a` can take is what it does everywhere. */
    @Test
    void theBoundLandsOnAValueThePositionCanTake() {
        AffineConstraint<String> rule =
                rule(weighing("a", 2, "b", 1), -9, Rel.LE, Granularity.DISCRETE);
        assertEquals(RationalCut.inclusive(num(4)),
                reduce(List.of(rule), between("b", 0, 5), Granularity.DISCRETE).atMost().get("a"),
                "`2a <= 9` leaves a at four and never at four and a half");
    }

    @Test
    void anEqualityIsReadFromBothSides() {
        AffineConstraint<String> rule =
                rule(weighing("a", 1, "b", 1, "c", 1), -10, Rel.EQ, Granularity.DISCRETE);
        Reduction.Tightened<String> found =
                reduce(List.of(rule), between("b", 1, 3, "c", 2, 4), Granularity.DISCRETE);
        assertEquals(RationalCut.inclusive(num(7)), found.atMost().get("a"));
        assertEquals(RationalCut.inclusive(num(3)), found.atLeast().get("a"));
    }

    /**
     * A hole says which side of it the sum lies only where something else has already ruled out one
     * side. With nothing to side it, it bounds nothing — a range cannot leave one value out of its
     * own middle.
     */
    @Test
    void aHoleWithNothingToSideItBoundsNothing() {
        AffineConstraint<String> hole =
                rule(weighing("a", 1, "b", 1), -10, Rel.NE, Granularity.DISCRETE);
        Reduction.Tightened<String> found =
                reduce(List.of(hole), between("b", 0, 5), Granularity.DISCRETE);
        assertTrue(found.atLeast().isEmpty() && found.atMost().isEmpty(),
                "nothing bounds a, so the sum can fall either side of ten");
    }

    /** Where the sum cannot go below the value, it goes above it. */
    @Test
    void aHoleAtTheFloorLiftsIt() {
        AffineConstraint<String> hole =
                rule(weighing("a", 1), 0, Rel.NE, Granularity.DISCRETE);
        assertEquals(RationalCut.inclusive(num(1)),
                reduce(List.of(hole), between("a", 0, 5), Granularity.DISCRETE)
                        .atLeast().get("a"));
    }

    /** And where it cannot go above, it goes below. */
    @Test
    void aHoleAtTheCeilingLowersIt() {
        AffineConstraint<String> hole =
                rule(weighing("a", 1), -5, Rel.NE, Granularity.DISCRETE);
        assertEquals(RationalCut.inclusive(num(4)),
                reduce(List.of(hole), between("a", 0, 5), Granularity.DISCRETE)
                        .atMost().get("a"));
    }

    /** A hole over several positions is sided by what the others are left, like any other rule. */
    @Test
    void aHoleOverSeveralPositionsIsSidedByWhatTheOthersLeave() {
        AffineConstraint<String> hole =
                rule(weighing("a", 1, "b", 1), -10, Rel.NE, Granularity.DISCRETE);
        assertEquals(RationalCut.inclusive(num(9)),
                reduce(List.of(hole), between("a", 0, 5, "b", 0, 5), Granularity.DISCRETE)
                        .atMost().get("a"),
                "a + b cannot exceed ten and is not ten, so it is under ten — and what that leaves"
                        + " a is read with b at the least it can be, since a bound that held only"
                        + " at b's greatest would not be a bound on a");
    }

    @Test
    void aHoleAtTheOnlyValueLeftLeavesNothing() {
        AffineConstraint<String> hole =
                rule(weighing("a", 1), -3, Rel.NE, Granularity.DISCRETE);
        assertInstanceOf(Reduction.NothingIsLeft.class,
                AffineReduction.over(reading(List.of(hole), between("a", 3, 3)),
                        atom -> Granularity.DISCRETE));
    }

    /** A rule over several positions can empty a system the difference bounds see nothing wrong
     *  with, and a reader handed two ends that have crossed has to be told. */
    @Test
    void aRuleThatLeavesAPositionNothingSaysSo() {
        AffineConstraint<String> rule =
                rule(weighing("a", 1, "b", 1), -5, Rel.LE, Granularity.DISCRETE);
        assertInstanceOf(Reduction.NothingIsLeft.class,
                AffineReduction.over(reading(List.of(rule), between("a", 10, 20, "b", 10, 20)),
                        atom -> Granularity.DISCRETE));
    }

    // --- against the points ------------------------------------------------------------------------

    /**
     * No point the rules admit is ever left outside what this derives, over rules and boxes drawn at
     * random. The direction asserted is the only one that matters: a bound too tight refuses a row a
     * model admits, and a bound too loose merely says less than it could.
     */
    @Test
    void noPointTheRulesAdmitIsEverRefused() {
        Random dice = new Random(4800);
        int narrowed = 0;
        for (int round = 0; round < CASES; round++) {
            List<Written> written = someRules(dice);
            List<AffineConstraint<String>> stated = read(written);
            Box<String> from = between("a", LOW, HIGH, "b", LOW, HIGH, "c", LOW, HIGH);
            List<Map<String, Integer>> admitted = pointsSatisfying(written);

            FormReach<String> reading = reading(stated, from);
            if (reading == null) {
                assertTrue(admitted.isEmpty(),
                        () -> "the differences hold nothing, but " + written + " admits " + admitted);
                continue;
            }
            Reduction<String> found = AffineReduction.over(reading, atom -> Granularity.DISCRETE);
            if (found instanceof Reduction.NothingIsLeft) {
                assertTrue(admitted.isEmpty(),
                        () -> "said nothing is left, but " + written + " admits " + admitted);
                continue;
            }
            Reduction.Tightened<String> tightened = (Reduction.Tightened<String>) found;
            Box<String> after = from.meeting(tightened.atLeast(), tightened.atMost());
            if (!tightened.atLeast().isEmpty() || !tightened.atMost().isEmpty()) {
                narrowed++;
            }
            for (Map<String, Integer> point : admitted) {
                for (String position : POSITIONS) {
                    Rational at = num(point.get(position));
                    assertTrue(admits(after.leastOf(position), at, false)
                                    && admits(after.mostOf(position), at, true),
                            () -> "refused a point the rules admit: " + point + " under " + written
                                    + " left " + position + " in [" + after.leastOf(position)
                                    + ", " + after.mostOf(position) + "]");
                }
            }
            // Reductive: nothing came back wider than it went in.
            for (String position : POSITIONS) {
                assertEquals(after.leastOf(position),
                        RationalCut.tighterLower(from.leastOf(position), after.leastOf(position)));
                assertEquals(after.mostOf(position),
                        RationalCut.tighterUpper(from.mostOf(position), after.mostOf(position)));
            }
        }
        assertTrue(narrowed > CASES / 10,
                "only " + narrowed + " of " + CASES + " narrowed anything, so this checked little");
    }

    /** And the same answers whatever order the rules arrived in. */
    @Test
    void theOrderTheRulesArrivedInIsNotPartOfTheAnswer() {
        Random dice = new Random(16);
        for (int round = 0; round < CASES; round++) {
            List<AffineConstraint<String>> stated = read(someRules(dice));
            Box<String> from = between("a", LOW, HIGH, "b", LOW, HIGH, "c", LOW, HIGH);
            List<AffineConstraint<String>> shuffled = new ArrayList<>(stated);
            Collections.shuffle(shuffled, dice);

            FormReach<String> asRead = reading(stated, from);
            FormReach<String> reread = reading(shuffled, from);
            if (asRead == null || reread == null) {
                continue;   // the differences hold nothing, which the closure answers before a round
            }
            Reduction<String> asWritten =
                    AffineReduction.over(asRead, atom -> Granularity.DISCRETE);
            Reduction<String> reordered =
                    AffineReduction.over(reread, atom -> Granularity.DISCRETE);
            assertEquals(asWritten, reordered,
                    () -> "the reduction moved when the rules were reordered: " + stated);
        }
    }

    /** Monotone: a narrower box never yields a wider answer. */
    @Test
    void aNarrowerBoxNeverSaysLess() {
        Random dice = new Random(600);
        for (int round = 0; round < CASES; round++) {
            List<AffineConstraint<String>> stated = read(someRules(dice));
            Box<String> wide = between("a", LOW, HIGH, "b", LOW, HIGH, "c", LOW, HIGH);
            Box<String> narrow = between("a", LOW + 1, HIGH - 1, "b", LOW + 1, HIGH - 1,
                    "c", LOW + 1, HIGH - 1);

            FormReach<String> readWide = reading(stated, wide);
            FormReach<String> readNarrow = reading(stated, narrow);
            if (readWide == null || readNarrow == null) {
                continue;   // the differences hold nothing, which the closure answers before a round
            }
            Reduction<String> overWide =
                    AffineReduction.over(readWide, atom -> Granularity.DISCRETE);
            Reduction<String> overNarrow =
                    AffineReduction.over(readNarrow, atom -> Granularity.DISCRETE);
            if (!(overWide instanceof Reduction.Tightened<String> loose)) {
                continue;   // the wider box was already empty, so there is nothing wider to be
            }
            if (!(overNarrow instanceof Reduction.Tightened<String> tight)) {
                continue;
            }
            for (String position : POSITIONS) {
                RationalCut looseHigh = loose.atMost().get(position);
                RationalCut tightHigh = tight.atMost().get(position);
                if (looseHigh != null && tightHigh != null) {
                    assertEquals(tightHigh, RationalCut.tighterUpper(looseHigh, tightHigh),
                            () -> "a narrower box said less above " + position);
                }
                RationalCut looseLow = loose.atLeast().get(position);
                RationalCut tightLow = tight.atLeast().get(position);
                if (looseLow != null && tightLow != null) {
                    assertEquals(tightLow, RationalCut.tighterLower(looseLow, tightLow),
                            () -> "a narrower box said less below " + position);
                }
            }
        }
    }

    @Test
    void aBoxSaysNothingAboutAPositionNobodyBounded() {
        assertFalse(Box.<String>unbounded().positions().contains("a"));
        assertTrue(Box.<String>unbounded().holdsAValueAt("a"));
        assertNull(Box.<String>unbounded().mostOf("a"));
    }

    private static boolean admits(RationalCut cut, Rational value, boolean above) {
        if (cut == null) {
            return true;
        }
        int order = value.compareTo(cut.at());
        return above ? (order < 0 || (order == 0 && cut.inclusive()))
                : (order > 0 || (order == 0 && cut.inclusive()));
    }

    /** Rules over two or three positions, weighted unevenly, which is what the difference bounds
     *  cannot hold and what this exists for. */
    private static List<Written> someRules(Random dice) {
        List<Written> out = new ArrayList<>();
        int howMany = 1 + dice.nextInt(3);
        for (int i = 0; i < howMany; i++) {
            Map<String, Rational> coefs = new LinkedHashMap<>();
            for (String position : POSITIONS) {
                int weight = dice.nextInt(7) - 3;
                if (weight != 0) {
                    coefs.put(position, num(weight));
                }
            }
            if (coefs.isEmpty()) {
                continue;
            }
            long constant = dice.nextInt(21) - 10;
            out.add(new Written(coefs, num(constant), someRelation(dice)));
        }
        return out;
    }


    /**
     * One of the relations a rule can be written with, taken from the enum rather than from a list.
     *
     * <p>Written out, this was a copy of {@link Rel} that nothing compared against it, and the
     * {@code default} arm meant it went on compiling however far the two drifted. They did: one
     * generator here left out {@code /=} and the one beside it left out {@code /=} and {@code >},
     * so the properties these tests hold — sound against the points, the same whatever order the
     * rules arrived in, never wider for a narrower box — were never asked of a rule of that shape.
     * The reading that decides which side of a hole a sum falls went unchecked by all three.
     *
     * <p>Taken from the values, a relation added to the language is generated here without anyone
     * remembering to add it.
     */
    private static Rel someRelation(Random dice) {
        Rel[] all = Rel.values();
        return all[dice.nextInt(all.length)];
    }

    private static List<AffineConstraint<String>> read(List<Written> written) {
        List<AffineConstraint<String>> out = new ArrayList<>();
        for (Written each : written) {
            if (AffineConstraint.of(each.coefs(), each.constant(), each.rel(),
                    atom -> Granularity.DISCRETE) instanceof Read.Stated<String> stated) {
                out.add(stated.constraint());
            }
        }
        return out;
    }

    private static List<Map<String, Integer>> pointsSatisfying(List<Written> written) {
        List<Map<String, Integer>> out = new ArrayList<>();
        for (int a = LOW; a <= HIGH; a++) {
            for (int b = LOW; b <= HIGH; b++) {
                for (int c = LOW; c <= HIGH; c++) {
                    Map<String, Integer> point = new LinkedHashMap<>();
                    point.put("a", a);
                    point.put("b", b);
                    point.put("c", c);
                    if (written.stream().allMatch(rule -> holdsAt(rule, point))) {
                        out.add(point);
                    }
                }
            }
        }
        return out;
    }

    private static boolean holdsAt(Written rule, Map<String, Integer> point) {
        Rational total = rule.constant();
        for (Map.Entry<String, Rational> each : rule.coefs().entrySet()) {
            total = total.plus(each.getValue().times(num(point.get(each.getKey()))));
        }
        int sign = total.signum();
        return switch (rule.rel()) {
            case LE -> sign <= 0;
            case LT -> sign < 0;
            case GE -> sign >= 0;
            case GT -> sign > 0;
            case EQ -> sign == 0;
            case NE -> sign != 0;
        };
    }
}
