package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.AffineConstraint.Read;
import souther.compiler.numeric.AffineReduction.Reduction;
import souther.compiler.numeric.RulesAsWritten.Written;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;
import static souther.compiler.numeric.RulesAsWritten.OVER_THREE;
import static souther.compiler.numeric.RulesAsWritten.admits;
import static souther.compiler.numeric.RulesAsWritten.pointsSatisfying;
import static souther.compiler.numeric.RulesAsWritten.relationsIn;
import static souther.compiler.numeric.RulesAsWritten.everyOrder;

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
 *
 * <p>Over the systems of {@link RulesAsWritten#OVER_THREE}, each written for a step the reduction
 * takes: the rest of a rule read without the position being bounded, ends that meet at one value,
 * a cycle of differences summing to nought, a hole sided by what is known and one that is not, and
 * two rules or two premises bounding one thing, which a reader letting the later one win answers
 * differently in some order. Each is given in every order its rules have.
 */
class ARuleOverSeveralPositionsNarrowsEachOfThemTest {

    private static final List<String> POSITIONS = List.of("a", "b", "c");
    private static final int LOW = -4;
    private static final int HIGH = 4;

    private static ExactRatio num(long whole) {
        return ExactRatio.of(whole);
    }

    private static Map<String, ExactRatio> weighing(Object... pairs) {
        Map<String, ExactRatio> out = new LinkedHashMap<>();
        for (int i = 0; i < pairs.length; i += 2) {
            out.put((String) pairs[i], num((Integer) pairs[i + 1]));
        }
        return out;
    }


    /** The constraint {@code read} states, where it states one. Asked through the reading's own
     *  type, so that what comes back is a constraint over the same positions the reading was of. */
    private static AffineConstraint<String> stated(Read<String> read) {
        assertInstanceOf(Read.Stated.class, read);
        return ((Read.Stated<String>) read).constraint();
    }

    private static AffineConstraint<String> rule(Map<String, ExactRatio> coefs, long constant,
                                                 Rel rel, Granularity spacing) {
        return stated(AffineConstraint.of(coefs, num(constant), rel, atom -> spacing));
    }

    private static Box<String> between(Object... triples) {
        Map<String, ExactCut> least = new LinkedHashMap<>();
        Map<String, ExactCut> most = new LinkedHashMap<>();
        for (int i = 0; i < triples.length; i += 3) {
            String atom = (String) triples[i];
            least.put(atom, ExactCut.inclusive(num((Integer) triples[i + 1])));
            most.put(atom, ExactCut.inclusive(num((Integer) triples[i + 2])));
        }
        return new Box<>(least, most);
    }

    private static Reduction.Tightened<String> reduce(List<AffineConstraint<String>> rules,
                                                      Box<String> from, Granularity spacing) {
        Reduction<String> reduced = AffineReduction.over(reading(rules, from), atom -> spacing,
                CanonicalOrder.asTheyAreSpelled());
        assertInstanceOf(Reduction.Tightened.class, reduced);
        return (Reduction.Tightened<String>) reduced;
    }

    /**
     * The rules read against {@code from}, which is what a round of the closure hands the reduction —
     * or null where the differences alone already hold nothing, which is where a round is never
     * reached.
     */
    private static FormReach<String> reading(List<AffineConstraint<String>> rules, Box<String> from) {
        DifferenceBounds<String> differences =
                DifferenceBounds.over(rules, CanonicalOrder.asTheyAreSpelled());
        return differences.holdsNothing() ? null
                : FormReach.over(rules, from, differences, CanonicalOrder.asTheyAreSpelled());
    }

    // --- the issue's example -----------------------------------------------------------------------

    @Test
    void theRuleAndWhatTheOthersAreLeftBoundThePosition() {
        AffineConstraint<String> budget =
                rule(weighing("straw", 300, "choco", 600), -4800, Rel.LE, Granularity.DISCRETE);
        Box<String> from = between("straw", 0, 1000, "choco", 0, 6);

        Reduction.Tightened<String> found =
                reduce(List.of(budget), from, Granularity.DISCRETE);

        assertEquals(ExactCut.inclusive(num(16)), found.atMost().get("straw"),
                "choco is never below nought, so the rule leaves straw at most sixteen");
        assertEquals(ExactCut.inclusive(num(8)), found.atMost().get("choco"),
                "and straw is never below nought, so it leaves choco at most eight");
        assertNull(found.atLeast().get("straw"), "and says nothing below, which the rule does not");
    }

    /** What the other positions are left is read from the box, so a tighter box says more. */
    @Test
    void whatTheOthersAreLeftIsWhatTheBoxSays() {
        AffineConstraint<String> budget =
                rule(weighing("straw", 300, "choco", 600), -4800, Rel.LE, Granularity.DISCRETE);
        assertEquals(ExactCut.inclusive(num(4)),
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
        assertEquals(ExactCut.inclusive(num(14)),
                reduce(List.of(rule), between("a", 0, 100, "b", 0, 5, "c", 1, 3),
                        Granularity.DISCRETE).atMost().get("a"),
                "b is at most five and c at least one, so a is at most 10 + 5 - 1");
    }

    @Test
    void aPositionWithoutTheEndThatMattersLeavesTheRuleSayingNothing() {
        AffineConstraint<String> rule =
                rule(weighing("a", 1, "b", 1), -10, Rel.LE, Granularity.DISCRETE);
        Map<String, ExactCut> nothing = Map.of();
        Reduction.Tightened<String> found = reduce(List.of(rule),
                new Box<>(nothing, nothing), Granularity.DISCRETE);
        assertTrue(found.atLeast().isEmpty() && found.atMost().isEmpty(),
                "nothing bounds b below, so the sum bounds a at nothing");
    }

    @Test
    void aBoundReachedByNothingMakesWhatFollowsStrict() {
        AffineConstraint<String> rule =
                rule(weighing("a", 1, "b", 1), -10, Rel.LE, Granularity.DENSE);
        Box<String> from = new Box<>(Map.of("b", ExactCut.exclusive(num(2))), Map.of());
        assertEquals(ExactCut.exclusive(num(8)),
                reduce(List.of(rule), from, Granularity.DENSE).atMost().get("a"),
                "b never quite reaches two, so a never quite reaches eight");
    }

    /** Turning `k·a <= w - m` into a bound on `a` is handed back to the one place that decides it,
     *  so what it does about the values `a` can take is what it does everywhere. */
    @Test
    void theBoundLandsOnAValueThePositionCanTake() {
        AffineConstraint<String> rule =
                rule(weighing("a", 2, "b", 1), -9, Rel.LE, Granularity.DISCRETE);
        assertEquals(ExactCut.inclusive(num(4)),
                reduce(List.of(rule), between("b", 0, 5), Granularity.DISCRETE).atMost().get("a"),
                "`2a <= 9` leaves a at four and never at four and a half");
    }

    @Test
    void anEqualityIsReadFromBothSides() {
        AffineConstraint<String> rule =
                rule(weighing("a", 1, "b", 1, "c", 1), -10, Rel.EQ, Granularity.DISCRETE);
        Reduction.Tightened<String> found =
                reduce(List.of(rule), between("b", 1, 3, "c", 2, 4), Granularity.DISCRETE);
        assertEquals(ExactCut.inclusive(num(7)), found.atMost().get("a"));
        assertEquals(ExactCut.inclusive(num(3)), found.atLeast().get("a"));
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
        assertEquals(ExactCut.inclusive(num(1)),
                reduce(List.of(hole), between("a", 0, 5), Granularity.DISCRETE)
                        .atLeast().get("a"));
    }

    /** And where it cannot go above, it goes below. */
    @Test
    void aHoleAtTheCeilingLowersIt() {
        AffineConstraint<String> hole =
                rule(weighing("a", 1), -5, Rel.NE, Granularity.DISCRETE);
        assertEquals(ExactCut.inclusive(num(4)),
                reduce(List.of(hole), between("a", 0, 5), Granularity.DISCRETE)
                        .atMost().get("a"));
    }

    /** A hole over several positions is sided by what the others are left, like any other rule. */
    @Test
    void aHoleOverSeveralPositionsIsSidedByWhatTheOthersLeave() {
        AffineConstraint<String> hole =
                rule(weighing("a", 1, "b", 1), -10, Rel.NE, Granularity.DISCRETE);
        assertEquals(ExactCut.inclusive(num(9)),
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
                        atom -> Granularity.DISCRETE, CanonicalOrder.asTheyAreSpelled()));
    }

    /** A rule over several positions can empty a system the difference bounds see nothing wrong
     *  with, and a reader handed two ends that have crossed has to be told. */
    @Test
    void aRuleThatLeavesAPositionNothingSaysSo() {
        AffineConstraint<String> rule =
                rule(weighing("a", 1, "b", 1), -5, Rel.LE, Granularity.DISCRETE);
        assertInstanceOf(Reduction.NothingIsLeft.class,
                AffineReduction.over(reading(List.of(rule), between("a", 10, 20, "b", 10, 20)),
                        atom -> Granularity.DISCRETE, CanonicalOrder.asTheyAreSpelled()));
    }

    // --- against the points ------------------------------------------------------------------------

    /**
     * No point the rules admit is ever left outside what this derives. The direction asserted is the
     * only one that matters: a bound too tight refuses a row a model admits, and a bound too loose
     * merely says less than it could.
     */
    @Test
    void noPointTheRulesAdmitIsEverRefused() {
        assertEquals(Set.of(Rel.values()), relationsIn(OVER_THREE),
                "a relation no system is written with is one no reading of it is asked about");
        int narrowed = 0;
        int emptied = 0;
        for (List<Written> written : OVER_THREE) {
            List<AffineConstraint<String>> stated = read(written);
            Box<String> from = between("a", LOW, HIGH, "b", LOW, HIGH, "c", LOW, HIGH);
            List<Map<String, Integer>> admitted = pointsSatisfying(written, POSITIONS, LOW, HIGH);

            FormReach<String> reading = reading(stated, from);
            if (reading == null) {
                assertTrue(admitted.isEmpty(),
                        () -> "the differences hold nothing, but " + written + " admits " + admitted);
                continue;
            }
            Reduction<String> found = AffineReduction.over(reading, atom -> Granularity.DISCRETE,
                    CanonicalOrder.asTheyAreSpelled());
            if (found instanceof Reduction.NothingIsLeft) {
                assertTrue(admitted.isEmpty(),
                        () -> "said nothing is left, but " + written + " admits " + admitted);
                emptied++;
                continue;
            }
            Reduction.Tightened<String> tightened = (Reduction.Tightened<String>) found;
            Box<String> after = from.meeting(tightened.atLeast(), tightened.atMost());
            if (!tightened.atLeast().isEmpty() || !tightened.atMost().isEmpty()) {
                narrowed++;
            }
            // A box holds every admitted point exactly when, at each position, it holds the least
            // and the greatest value an admitted point has there — so those two points are the
            // ones asked about.
            for (String position : POSITIONS) {
                Map<String, Integer> lowest = null;
                Map<String, Integer> highest = null;
                for (Map<String, Integer> point : admitted) {
                    if (lowest == null || point.get(position) < lowest.get(position)) {
                        lowest = point;
                    }
                    if (highest == null || point.get(position) > highest.get(position)) {
                        highest = point;
                    }
                }
                if (lowest == null) {
                    continue;
                }
                for (Map<String, Integer> point : List.of(lowest, highest)) {
                    ExactRatio at = num(point.get(position));
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
                        ExactCut.tighterLower(from.leastOf(position), after.leastOf(position)));
                assertEquals(after.mostOf(position),
                        ExactCut.tighterUpper(from.mostOf(position), after.mostOf(position)));
            }
        }
        assertTrue(narrowed > 0 && emptied > 0, "narrowed " + narrowed + " and emptied " + emptied
                + " of " + OVER_THREE.size() + ", so one of the two was never checked");
    }

    /** And the same answers whatever order the rules arrived in, which is every order they have. */
    @Test
    void theOrderTheRulesArrivedInIsNotPartOfTheAnswer() {
        for (List<Written> written : OVER_THREE) {
            List<AffineConstraint<String>> stated = read(written);
            Box<String> from = between("a", LOW, HIGH, "b", LOW, HIGH, "c", LOW, HIGH);
            FormReach<String> asRead = reading(stated, from);
            if (asRead == null) {
                continue;   // the differences hold nothing, which the closure answers before a round
            }
            Reduction<String> asWritten = AffineReduction.over(asRead,
                    atom -> Granularity.DISCRETE, CanonicalOrder.asTheyAreSpelled());
            for (List<AffineConstraint<String>> shuffled : everyOrder(stated)) {
                FormReach<String> reread = reading(shuffled, from);
                assertTrue(reread != null,
                        () -> "the differences hold nothing only in another order: " + shuffled);
                Reduction<String> reordered =
                        AffineReduction.over(reread, atom -> Granularity.DISCRETE,
                                CanonicalOrder.asTheyAreSpelled());
                assertEquals(asWritten, reordered,
                        () -> "the reduction moved when the rules were reordered: " + shuffled);
            }
        }
    }

    /** Monotone: a narrower box never yields a wider answer. */
    @Test
    void aNarrowerBoxNeverSaysLess() {
        for (List<Written> written : OVER_THREE) {
            List<AffineConstraint<String>> stated = read(written);
            Box<String> wide = between("a", LOW, HIGH, "b", LOW, HIGH, "c", LOW, HIGH);
            Box<String> narrow = between("a", LOW + 1, HIGH - 1, "b", LOW + 1, HIGH - 1,
                    "c", LOW + 1, HIGH - 1);

            FormReach<String> readWide = reading(stated, wide);
            FormReach<String> readNarrow = reading(stated, narrow);
            if (readWide == null || readNarrow == null) {
                continue;   // the differences hold nothing, which the closure answers before a round
            }
            Reduction<String> overWide =
                    AffineReduction.over(readWide, atom -> Granularity.DISCRETE,
                            CanonicalOrder.asTheyAreSpelled());
            Reduction<String> overNarrow =
                    AffineReduction.over(readNarrow, atom -> Granularity.DISCRETE,
                            CanonicalOrder.asTheyAreSpelled());
            if (!(overWide instanceof Reduction.Tightened<String> loose)) {
                continue;   // the wider box was already empty, so there is nothing wider to be
            }
            if (!(overNarrow instanceof Reduction.Tightened<String> tight)) {
                continue;
            }
            for (String position : POSITIONS) {
                ExactCut looseHigh = loose.atMost().get(position);
                ExactCut tightHigh = tight.atMost().get(position);
                if (looseHigh != null && tightHigh != null) {
                    assertEquals(tightHigh, ExactCut.tighterUpper(looseHigh, tightHigh),
                            () -> "a narrower box said less above " + position);
                }
                ExactCut looseLow = loose.atLeast().get(position);
                ExactCut tightLow = tight.atLeast().get(position);
                if (looseLow != null && tightLow != null) {
                    assertEquals(tightLow, ExactCut.tighterLower(looseLow, tightLow),
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

    private static List<AffineConstraint<String>> read(List<Written> written) {
        return RulesAsWritten.read(written, atom -> Granularity.DISCRETE);
    }
}
