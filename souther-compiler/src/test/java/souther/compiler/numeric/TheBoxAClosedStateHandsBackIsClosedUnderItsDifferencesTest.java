package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.NumericDomain.Rel;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The box handed back is a fixed point of carrying it along the differences.
 *
 * <p>What rests on this is the reading of a range. A bound derived here is read back one position at
 * a time, and what makes those readings the whole of what the rules leave is that no difference can
 * still carry one of them onto another: with {@code a - b <= 0} and {@code b <= 3}, an {@code a} left
 * at 5 is a bound nothing has finished deriving. Stated as a property of the box rather than as a
 * step the derivation takes, because a step is something a later change can take somewhere else
 * while every reader goes on depending on what it established.
 *
 * <p>Held whether or not the rounds settled. The rounds are the outer refinement over rules the
 * differences cannot hold, and the box is carried along the differences at the end of each of them —
 * so running out of rounds leaves a box that is wider than the rules and still closed. Which is why
 * the certificate does not ask {@link ClosedState.Status}: what it needs is this, and this holds
 * either way.
 *
 * <p>The half where the rounds run out is written down rather than sampled. Over whole numbers in a
 * bounded box the descent stops on its own — each round takes some end at least a whole step in, and
 * there are finitely many steps to take — so the generated systems below never reach it, and a check
 * that hoped they would would be about one status while claiming both. What needs the budget is a
 * descent that never arrives, which takes values that fill.
 */
class TheBoxAClosedStateHandsBackIsClosedUnderItsDifferencesTest {

    private static final List<String> POSITIONS = List.of("a", "b", "c");
    private static final int CASES = 300;

    /**
     * No difference carries an end onto another position's end and finds it loose.
     *
     * <p>The property itself, in the terms it is about: {@code a - b <= d} with {@code b} at most
     * {@code h} puts {@code a} at most {@code h + d}, so an {@code a} left above that is one this
     * derivation has not finished. Read off the public answers rather than off the walk that
     * produces them.
     */
    @Test
    void noDifferenceLeavesAnEndLooserThanItCouldBe() {
        Random dice = new Random(907);
        int settled = 0;
        int exhausted = 0;
        for (int round = 0; round < CASES; round++) {
            ClosedState<String> closed = ClosedState.of(read(aSystem(dice), Granularity.DISCRETE),
                    atom -> Granularity.DISCRETE);
            if (closed.holdsNothing()) {
                continue;
            }
            if (closed.status() == ClosedState.Status.STABLE) { settled++; } else { exhausted++; }
            Box<String> box = closed.box();
            for (String here : POSITIONS) {
                for (String there : POSITIONS) {
                    if (here.equals(there)) {
                        continue;
                    }
                    RationalCut apart = closed.differences().differenceBound(here, there);
                    if (apart == null) {
                        continue;
                    }
                    RationalCut carried = box.mostOf(there) == null ? null
                            : RationalCut.meetingBoth(box.mostOf(there), apart);
                    assertEquals(RationalCut.tighterUpper(box.mostOf(here), carried),
                            box.mostOf(here),
                            () -> here + " - " + there + " is " + apart + " and " + there
                                    + " is at most " + box.mostOf(there) + ", which puts " + here
                                    + " at " + carried + " and the box left it at "
                                    + box.mostOf(here));

                    RationalCut back = closed.differences().differenceBound(there, here);
                    if (back == null || box.leastOf(there) == null) {
                        continue;
                    }
                    RationalCut below = new RationalCut(
                            box.leastOf(there).at().minus(back.at()),
                            box.leastOf(there).inclusive() && back.inclusive());
                    assertEquals(RationalCut.tighterLower(box.leastOf(here), below),
                            box.leastOf(here),
                            () -> there + " - " + here + " is " + back + " and " + there
                                    + " is at least " + box.leastOf(there) + ", which puts " + here
                                    + " at " + below + " and the box left it at "
                                    + box.leastOf(here));
                }
            }
        }
        assertTrue(settled > 0,
                "no system settled, so the property was checked about nothing: " + settled
                        + " settled and " + exhausted + " ran out of rounds");
    }

    /** And so carrying it again is carrying it nowhere, which is the same property said as a step. */
    @Test
    void carryingTheBoxAlongTheDifferencesAgainMovesNothing() {
        Random dice = new Random(1016);
        for (int round = 0; round < CASES; round++) {
            ClosedState<String> closed = ClosedState.of(read(aSystem(dice), Granularity.DISCRETE),
                    atom -> Granularity.DISCRETE);
            if (closed.holdsNothing()) {
                continue;
            }
            assertEquals(closed.box(), closed.boxCarriedAlongTheDifferences(),
                    "the box moved when it was carried along the differences a second time");
        }
    }

    /**
     * And where the rounds run out, said as one system rather than hoped for.
     *
     * <p>Two rules each halving what the other leaves — {@code 2x <= y} beside {@code 2y <= x} over
     * values that fill — descend by a quarter every round and never arrive, which is the case the
     * budget exists for. A third position is held a step from one of them, so that carrying the box
     * along the differences has something to carry: the property is about the relations, and a system
     * without one would hold it by having nothing to check.
     */
    @Test
    void aBoxTheRoundsRanOutOnIsClosedUnderTheDifferencesToo() {
        List<Written> system = new ArrayList<>();
        for (String position : List.of("x", "y")) {
            system.add(new Written(Map.of(position, Rational.ONE), Rational.ZERO, Rel.GE));
            system.add(new Written(Map.of(position, Rational.ONE), Rational.of(-100), Rel.LE));
        }
        system.add(new Written(Map.of("z", Rational.ONE), Rational.ZERO, Rel.GE));
        system.add(new Written(Map.of("z", Rational.ONE), Rational.of(-101), Rel.LE));
        system.add(new Written(halving("x", "y"), Rational.ZERO, Rel.LE));
        system.add(new Written(halving("y", "x"), Rational.ZERO, Rel.LE));
        system.add(new Written(apart("z", "x"), Rational.of(-1), Rel.LE));

        ClosedState<String> closed =
                ClosedState.of(read(system, Granularity.DENSE), atom -> Granularity.DENSE);

        assertEquals(ClosedState.Status.BUDGET_EXHAUSTED, closed.status(),
                "the point of this system is that the rounds do not settle it");
        assertFalse(closed.holdsNothing());
        assertEquals(closed.box(), closed.boxCarriedAlongTheDifferences(),
                "the rounds ran out and the box is a fixed point of the differences all the same");
        // `z - x <= 1` with `x` wherever the rounds left it, which is what carrying it along the
        // differences puts `z` at — and is where the box has it.
        assertEquals(closed.box().mostOf("x").at().plus(Rational.ONE),
                closed.box().mostOf("z").at(),
                "the difference did not reach `z` at the end the rounds left `x` at");
    }

    // --- the systems ------------------------------------------------------------------------------

    /** {@code 2·above - below}, a rule the differences cannot hold and the rounds have to read. */
    private static Map<String, Rational> halving(String above, String below) {
        Map<String, Rational> coefs = new LinkedHashMap<>();
        coefs.put(above, Rational.of(2));
        coefs.put(below, Rational.ONE.negated());
        return coefs;
    }

    /** {@code above - below}, which the differences hold exactly. */
    private static Map<String, Rational> apart(String above, String below) {
        Map<String, Rational> coefs = new LinkedHashMap<>();
        coefs.put(above, Rational.ONE);
        coefs.put(below, Rational.ONE.negated());
        return coefs;
    }

    private record Written(Map<String, Rational> coefs, Rational constant, Rel rel) {}

    /**
     * A handful of rules over positions bounded both ways, of both shapes.
     *
     * <p>Sums over three positions as well as bounds and differences, because those are what the
     * rounds are for: a system the differences hold in full settles in the first round and would
     * never reach a box the outer refinement had moved.
     */
    private static List<Written> aSystem(Random dice) {
        List<Written> out = new ArrayList<>();
        for (String position : POSITIONS) {
            out.add(new Written(Map.of(position, Rational.ONE), Rational.of(4), Rel.GE));
            out.add(new Written(Map.of(position, Rational.ONE), Rational.of(-4), Rel.LE));
        }
        int howMany = 2 + dice.nextInt(4);
        for (int i = 0; i < howMany; i++) {
            long threshold = -4 + dice.nextInt(9);
            boolean strict = dice.nextBoolean();
            Rel rel = strict ? Rel.LT : Rel.LE;
            switch (dice.nextInt(3)) {
                case 0 -> out.add(new Written(
                        Map.of(POSITIONS.get(dice.nextInt(3)), Rational.ONE),
                        Rational.of(-threshold), rel));
                case 1 -> {
                    String one = POSITIONS.get(dice.nextInt(3));
                    String other = POSITIONS.get(dice.nextInt(3));
                    if (one.equals(other)) {
                        continue;
                    }
                    Map<String, Rational> coefs = new LinkedHashMap<>();
                    coefs.put(one, Rational.ONE);
                    coefs.put(other, Rational.ONE.negated());
                    out.add(new Written(coefs, Rational.of(-threshold), rel));
                }
                // A sum the differences cannot hold, so the outer rounds have something to do.
                default -> {
                    Map<String, Rational> coefs = new LinkedHashMap<>();
                    coefs.put("a", Rational.ONE);
                    coefs.put("b", Rational.ONE);
                    coefs.put("c", dice.nextBoolean() ? Rational.ONE : Rational.ONE.negated());
                    out.add(new Written(coefs, Rational.of(-threshold), rel));
                }
            }
        }
        return out;
    }

    /**
     * The rules read, spaced the way the state that closes them will be told they are.
     *
     * <p>Given the spacing rather than assuming one. Reading a rule moves its bound onto a value the
     * form can take, so a system read as whole numbers and closed as decimals is two answers about
     * two systems — which the constructed one below is, being about a descent only decimals have.
     */
    private static List<AffineConstraint<String>> read(List<Written> written, Granularity spacing) {
        List<AffineConstraint<String>> out = new ArrayList<>();
        for (Written each : written) {
            AffineConstraint.Read<String> read = AffineConstraint.of(
                    each.coefs(), each.constant(), each.rel(), atom -> spacing);
            if (read instanceof AffineConstraint.Read.Stated<String> stated) {
                out.add(stated.constraint());
            }
        }
        return out;
    }
}
