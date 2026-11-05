package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * How many ways of choosing a case no comparison chosen on the way refutes as numbers is the count
 * a reader writing every way out comes to, whatever the cases share and however they are nested.
 *
 * <p>Held against a count made the other way: every way of choosing written out, and each asked
 * for one value of the number and one remainder of it meeting every comparison it chose. The cases
 * are drawn at random over comparisons of one number and of remainders of it moved by constants,
 * held together and as alternatives, with what one choice leads to shared by others — so a count
 * that read a shared case once for every state would come out wrong, as would one that forgot the
 * remainders or the number.
 */
class TheNumericallyConsistentWaysAreTheWaysNoNumberRefutesTest {

    private static final NumericTerm X = new NumericTerm.ValueOf(TermPath.of("x"));
    private static final Quantity NUMBER = new DecisionAtom.OfTheInput(X);
    private static final ValueName FLOOR_MOD = ValueName.Stdlib.operation("Int", "floorMod");
    private static final int DIVISOR = 7;

    /** The number against {@code at}, in {@code rel}, held or denied. */
    private static Proposition onTheNumber(Rel rel, int at, boolean holds) {
        return compared(Map.of(NUMBER, ExactRatio.ONE), -at, rel, holds);
    }

    /** The remainder of the number moved by {@code by}, against {@code at}. */
    private static Proposition onARemainder(int by, Rel rel, int at, boolean holds) {
        Quantity remainder = new Quantity.RemainderOfADividend(FLOOR_MOD,
                new LinearForm<>(ExactRatio.of(by), Map.of(NUMBER, ExactRatio.ONE)),
                BigInteger.valueOf(DIVISOR));
        return compared(Map.of(remainder, ExactRatio.ONE), -at, rel, holds);
    }

    private static Proposition compared(Map<Quantity, ExactRatio> coefs, int constant, Rel rel,
                                        boolean holds) {
        Relation.OneWay<Quantity> one = Relation.OneWay.of(
                new LinearForm<>(ExactRatio.of(constant), new LinkedHashMap<>(coefs)), rel);
        return new Proposition.Compared(new Relation.Affine(one.form(), one.proposition()),
                one.holds() == holds);
    }

    /** A comparison drawn at random: of the number, or of a remainder of it. */
    private static Proposition aComparison(Random random) {
        Rel rel = new Rel[] {Rel.GE, Rel.GT, Rel.EQ}[random.nextInt(3)];
        boolean holds = random.nextBoolean();
        return random.nextBoolean() ? onTheNumber(rel, random.nextInt(9) - 4, holds)
                : onARemainder(random.nextInt(9) - 4, rel, random.nextInt(DIVISOR), holds);
    }

    /** Cases drawn at random, each made of the ones made before it so that some are shared. */
    private static DecidingCase.Cases cases(Random random) {
        List<DecidingCase.Cases> made = new ArrayList<>();
        for (int at = 0; at < 6; at++) {
            made.add(new DecidingCase.Cases.One(random.nextInt(4) == 0
                    ? Proposition.all(List.of(aComparison(random), aComparison(random)))
                    : aComparison(random)));
        }
        for (int at = 0; at < 8; at++) {
            List<DecidingCase.Cases> parts = new ArrayList<>();
            for (int part = 0; part < 2 + random.nextInt(2); part++) {
                parts.add(made.get(random.nextInt(made.size())));
            }
            made.add(random.nextBoolean() ? new DecidingCase.Cases.EachOf(parts)
                    : new DecidingCase.Cases.Together(parts));
        }
        return made.getLast();
    }

    /** Every way of choosing a case of {@code cases}, as the conditions it chose. */
    private static List<List<Proposition>> ways(DecidingCase.Cases cases) {
        return cases.fold(new DecidingCase.Cases.Fold<List<List<Proposition>>>() {

            @Override
            public List<List<Proposition>> one(DecidingCase.Cases.One one) {
                return List.of(List.of(one.condition()));
            }

            @Override
            public List<List<Proposition>> eachOf(DecidingCase.Cases.EachOf node,
                                                  List<List<List<Proposition>>> alternatives) {
                List<List<Proposition>> out = new ArrayList<>();
                alternatives.forEach(out::addAll);
                return out;
            }

            @Override
            public List<List<Proposition>> together(DecidingCase.Cases.Together node,
                                                    List<List<List<Proposition>>> factors) {
                List<List<Proposition>> out = List.of(List.of());
                for (List<List<Proposition>> factor : factors) {
                    List<List<Proposition>> next = new ArrayList<>();
                    for (List<Proposition> before : out) {
                        for (List<Proposition> after : factor) {
                            List<Proposition> both = new ArrayList<>(before);
                            both.addAll(after);
                            next.add(both);
                        }
                    }
                    out = next;
                }
                return out;
            }

            @Override
            public List<List<Proposition>> notTakenApart(
                    DecidingCase.Cases.NotTakenApart notTakenApart) {
                return List.of(List.of());
            }
        });
    }

    /** The comparisons {@code conditions} state together. */
    private static List<Proposition.Compared> comparisonsIn(List<Proposition> conditions) {
        List<Proposition.Compared> out = new ArrayList<>();
        for (Proposition condition : conditions) {
            if (condition instanceof Proposition.All all) {
                all.parts().forEach(part -> out.add((Proposition.Compared) part));
            } else {
                out.add((Proposition.Compared) condition);
            }
        }
        return out;
    }

    /**
     * Whether some value of the number meets every comparison of it in {@code chosen}, and some
     * remainder of it every comparison of a remainder. Asked at the values that can tell them
     * apart: every constant compared with, halfway between each two, and past both ends.
     */
    private static boolean someValueMeets(List<Proposition.Compared> chosen) {
        List<Proposition.Compared> ofTheNumber = new ArrayList<>();
        List<Proposition.Compared> ofARemainder = new ArrayList<>();
        for (Proposition.Compared each : chosen) {
            Relation.Affine affine = (Relation.Affine) each.relation();
            (affine.form().coefs().containsKey(NUMBER) ? ofTheNumber : ofARemainder).add(each);
        }
        boolean number = false;
        for (int doubled = -20; doubled <= 20 && !number; doubled++) {
            ExactRatio x = ExactRatio.of(BigInteger.valueOf(doubled), BigInteger.TWO);
            number = ofTheNumber.stream().allMatch(each -> holdsAt(each, x));
        }
        boolean remainder = false;
        for (int residue = 0; residue < DIVISOR && !remainder; residue++) {
            int r = residue;
            remainder = ofARemainder.stream().allMatch(each -> holdsAtTheRemainder(each, r));
        }
        return number && remainder;
    }

    private static boolean holdsAt(Proposition.Compared comparison, ExactRatio x) {
        Relation.Affine affine = (Relation.Affine) comparison.relation();
        ExactRatio left = x.times(affine.form().coefs().get(NUMBER)).orNull()
                .plus(affine.form().constant()).orNull();
        return affine.proposition().holds(left.signum()) == comparison.holds();
    }

    /** Whether the comparison holds where the number leaves {@code residue} divided by the
     *  divisor. */
    private static boolean holdsAtTheRemainder(Proposition.Compared comparison, int residue) {
        Relation.Affine affine = (Relation.Affine) comparison.relation();
        Map.Entry<Quantity, ExactRatio> only = affine.form().coefs().entrySet().iterator().next();
        Quantity.RemainderOfADividend remainder = (Quantity.RemainderOfADividend) only.getKey();
        int moved = remainder.dividend().constant().floor().orNull().intValueExact();
        ExactRatio left = only.getValue().times(ExactRatio.of(Math.floorMod(residue + moved,
                DIVISOR))).orNull().plus(affine.form().constant()).orNull();
        return affine.proposition().holds(left.signum()) == comparison.holds();
    }

    private static BigInteger atMost(NumericallyConsistentWays.Counted counted) {
        return assertInstanceOf(NumericallyConsistentWays.Counted.AtMost.class, counted).ways();
    }

    @Test
    void theConsistentWaysAreTheWaysWrittenOutThatSomeValueMeets() {
        Random random = new Random(3042);
        int refuted = 0;
        for (int drawn = 0; drawn < 600; drawn++) {
            DecidingCase.Cases cases = cases(random);
            List<List<Proposition>> ways = ways(cases);
            long met = ways.stream().filter(way -> someValueMeets(comparisonsIn(way))).count();
            refuted += ways.size() - (int) met;
            assertEquals(BigInteger.valueOf(ways.size()),
                    cases.structuralWays(CaseCount.WAYS_A_COUNT_IS_HELD_TO),
                    "every way of choosing is counted once, however the cases share: " + cases);
            assertEquals(BigInteger.valueOf(met), atMost(NumericallyConsistentWays.of(cases)),
                    "a way is consistent exactly where some value meets what it chose: " + cases);
        }
        assertTrue(refuted > 0, "some way drawn is refuted, or nothing was asked");
    }

    @Test
    void choosingOneMoreComparisonFirstLeavesNoMoreWays() {
        Random random = new Random(4230);
        for (int drawn = 0; drawn < 300; drawn++) {
            DecidingCase.Cases cases = cases(random);
            BigInteger every = atMost(NumericallyConsistentWays.of(cases));
            Proposition first = aComparison(random);
            for (Proposition start : List.of(first, first.denied())) {
                NumericallyConsistentWays.State from =
                        NumericallyConsistentWays.State.NOTHING_CHOSEN.taking(start);
                BigInteger fewer = from == null ? BigInteger.ZERO
                        : atMost(NumericallyConsistentWays.of(cases, from));
                assertTrue(fewer.compareTo(every) <= 0, "a way chosen past " + start
                        + " is one of the ways, and no more of them hold: " + cases);
            }
        }
    }

    /**
     * Ordered boundaries: a choice of each side of every one of several rising bounds of one
     * number, held together, is as many ways as two to the power of the bounds, and the number
     * leaves one more way than there are bounds — one for each stretch between them, the number
     * being in exactly one.
     */
    @Test
    void boundsOfOneNumberLeaveAWayForEachStretchBetweenThem() {
        for (int bounds = 1; bounds <= 12; bounds++) {
            List<DecidingCase.Cases> choices = new ArrayList<>();
            for (int at = 0; at < bounds; at++) {
                Proposition above = onTheNumber(Rel.GE, at * 10, true);
                choices.add(new DecidingCase.Cases.EachOf(List.of(
                        new DecidingCase.Cases.One(above),
                        new DecidingCase.Cases.One(above.denied()))));
            }
            CaseCount counted = CaseCount.of(new DecidingCase.Cases.Together(choices));
            assertEquals(new CaseCount.Ways.Exactly(BigInteger.TWO.pow(bounds)),
                    counted.structuralWays());
            assertEquals(new NumericallyConsistentWays.Counted.AtMost(
                    BigInteger.valueOf(bounds + 1)), counted.numericallyConsistentWays(),
                    bounds + " rising bounds of one number");
        }
    }

    /**
     * Correlated remainders: a choice of whether each of several remainders of one number moved by
     * one more is nought, held together, is as many ways as two to the power of the remainders, and
     * the number leaves no more ways than it has remainders — each remainder of it settles every
     * one of them.
     */
    @Test
    void remaindersOfOneNumberMovedApartLeaveAWayForEachRemainderAtMost() {
        for (int moved = 1; moved <= 12; moved++) {
            List<DecidingCase.Cases> choices = new ArrayList<>();
            for (int by = 0; by < moved; by++) {
                Proposition nought = onARemainder(by, Rel.EQ, 0, true);
                choices.add(new DecidingCase.Cases.EachOf(List.of(
                        new DecidingCase.Cases.One(nought),
                        new DecidingCase.Cases.One(nought.denied()))));
            }
            CaseCount counted = CaseCount.of(new DecidingCase.Cases.Together(choices));
            assertEquals(new CaseCount.Ways.Exactly(BigInteger.TWO.pow(moved)),
                    counted.structuralWays());
            // One way for each remainder the number may leave, and one more while some remainder
            // makes none of them nought.
            int left = Math.min(DIVISOR, moved + 1);
            assertEquals(new NumericallyConsistentWays.Counted.AtMost(BigInteger.valueOf(left)),
                    counted.numericallyConsistentWays(), moved + " remainders moved apart");
        }
    }

    @Test
    void pastTheStatesACountIsTakenInNothingIsCounted() {
        // One choice of each side of a line for each of seventeen numbers, every way consistent and
        // every one leaving the numbers a state of its own.
        List<DecidingCase.Cases> choices = new ArrayList<>();
        for (int at = 0; at < 17; at++) {
            Quantity number = new DecisionAtom.OfTheInput(
                    new NumericTerm.ValueOf(TermPath.of("x" + at)));
            Proposition above = compared(Map.of(number, ExactRatio.ONE), 0, Rel.GE, true);
            choices.add(new DecidingCase.Cases.EachOf(List.of(
                    new DecidingCase.Cases.One(above),
                    new DecidingCase.Cases.One(above.denied()))));
        }
        DecidingCase.Cases cases = new DecidingCase.Cases.Together(choices);
        assertEquals(new CaseCount.Ways.Exactly(BigInteger.TWO.pow(17)),
                CaseCount.of(cases).structuralWays());
        assertEquals(new NumericallyConsistentWays.Counted.NotCounted(
                        NumericallyConsistentWays.WhyNotCounted.STATES_A_COUNT_IS_TAKEN_IN),
                NumericallyConsistentWays.of(cases),
                "more states than a count is taken in is no count, and says so");
    }

    @Test
    void pastTheWaysACountIsHeldToTheCountSaysMore() {
        // Two ways at each of eleven steps, the same rest held twice under each: as many ways as
        // two to the power of two to the power of eleven, every one of them consistent.
        DecidingCase.Cases rest = new DecidingCase.Cases.One(new Proposition.Always(true));
        for (int step = 0; step < 11; step++) {
            DecidingCase.Cases twice = new DecidingCase.Cases.Together(List.of(rest, rest));
            rest = new DecidingCase.Cases.EachOf(List.of(twice, twice));
        }
        CaseCount counted = CaseCount.of(rest);
        assertEquals(new CaseCount.Ways.MoreThan(CaseCount.WAYS_A_COUNT_IS_HELD_TO),
                counted.structuralWays());
        assertEquals(new NumericallyConsistentWays.Counted.NotCounted(
                        NumericallyConsistentWays.WhyNotCounted.WAYS_A_COUNT_IS_HELD_TO),
                counted.numericallyConsistentWays());
    }
}
