package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.ACompiledModel;
import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;
import java.util.function.BiFunction;
import java.util.function.BiPredicate;
import java.util.stream.Stream;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a run got past narrows a region by every constraint the region is not shown to hold
 * already ({@link Reachability.Reaching#narrowedPast}): a constraint is left out only where every
 * row of the region is shown to meet it, and so a run that leaves the region no row is said to.
 *
 * <p>A constraint of one number is shown held where the number's run is shown and does not move.
 * Where it is shown on neither side — a region a comparison of several numbers narrowed — not
 * moving is no proof, and the constraint is asked as one of several numbers is.
 *
 * <p>Held against taking every constraint of the run in as it stands, over regions and runs drawn
 * at random from comparisons of two numbers and of their sum and difference: whether no row is
 * left, and which rows are, row by row against what the constraints say of each, in every order
 * the run may take them in, holes among them.
 */
class WhatARunGotPastIsLeftOutOfARegionOnlyWhereTheRegionIsShownToHoldItTest {

    private static final NumericTerm.FromOnePosition A =
            new NumericTerm.ValueOf(TermPath.of("r").then("a"));
    private static final NumericTerm.FromOnePosition D =
            new NumericTerm.ValueOf(TermPath.of("r").then("d"));

    private static final Rel[] RELS = {Rel.GE, Rel.GT, Rel.LE, Rel.LT};

    /** {@code constant} plus the sum of {@code terms}, in {@code rel} to nought. */
    private static TakenConstraint compared(int constant, Rel rel, NumericTerm... terms) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        for (NumericTerm each : terms) {
            coefs.put(each, ExactRatio.ONE);
        }
        return new TakenConstraint.Affine(new LinearForm<>(ExactRatio.of(constant), coefs), rel);
    }

    /** A comparison of one of the numbers, their sum or their difference, with a constant. */
    private static TakenConstraint aConstraint(Random random) {
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        switch (random.nextInt(4)) {
            case 0 -> coefs.put(A, ExactRatio.ONE);
            case 1 -> coefs.put(D, ExactRatio.ONE);
            case 2 -> {
                coefs.put(A, ExactRatio.ONE);
                coefs.put(D, ExactRatio.ONE);
            }
            default -> {
                coefs.put(A, ExactRatio.ONE);
                coefs.put(D, ExactRatio.of(-1));
            }
        }
        return new TakenConstraint.Affine(
                new LinearForm<>(ExactRatio.of(random.nextInt(41) - 20), coefs),
                RELS[random.nextInt(RELS.length)]);
    }

    private static List<TakenConstraint> some(Random random, int least, int most) {
        List<TakenConstraint> out = new ArrayList<>();
        for (int at = 0, n = least + random.nextInt(most - least + 1); at < n; at++) {
            out.add(aConstraint(random));
        }
        return out;
    }

    private static DemandReading.Answered ofTheRun(List<TakenConstraint> onTheWay,
                                                   List<TakenConstraint> ofTheRelation) {
        return new DemandReading.Answered(onTheWay, ofTheRelation, List.of(), false, List.of(),
                List.of());
    }

    private static SearchRegion declared() {
        Compilation compilation = ACompiledModel.answered("""
                module m

                data R = { a: Int, d: Int }
                data Yes

                behavior f : (r: R) -> Yes
                let f (r) = Yes
                """);
        var inputs = compilation.db().ask(new Adequacy.Inputs("m")).value().get("f");
        assertNotNull(inputs, "the model under test compiles");
        return inputs.reading(RuleReadings.of(compilation, "m")).quantities().region();
    }

    /**
     * A region a sum of the two numbers narrows shows no run of either, and a run that holds one
     * of them below nought and above eight leaves it no row: both are taken in. And one the
     * region is shown to hold, the number below a hundred where the region holds it at five or
     * less, is left out.
     */
    @Test
    void aBoundOfOneNumberIsTakenInWhereTheRegionShowsNoRunOfIt() {
        SearchRegion bySum = TakenConstraint.narrowedBy(
                List.of(compared(13, Rel.GE, A, D)), declared());
        assertEquals(null, bySum.wholeRunOf(D), "no run of the number is shown");
        TakenConstraint below = compared(0, Rel.LT, D);
        TakenConstraint above = compared(-8, Rel.GT, D);

        Reachability.Reaching.NarrowedPast past = Reachability.Reaching.narrowedPast(bySum,
                ofTheRun(List.of(below, above), List.of()));
        assertEquals(List.of(below, above), past.narrowing(), "both taken in");
        assertTrue(past.leavesNone(), "and no row is left");

        SearchRegion atMostFive = TakenConstraint.narrowedBy(
                List.of(compared(-5, Rel.LE, D)), bySum);
        TakenConstraint underAHundred = compared(-100, Rel.LT, D);
        assertEquals(List.of(), Reachability.Reaching.narrowedPast(atMostFive,
                        ofTheRun(List.of(underAHundred), List.of())).narrowing(),
                "a bound every row of the region is shown to meet is left out");
    }

    /**
     * A hole inside a number's run leaves the number no one run, which moves it, and is taken in;
     * the value is then out of the region and the ones beside it are not.
     */
    @Test
    void aHoleInsideARunIsTakenIn() {
        SearchRegion upToTen = TakenConstraint.narrowedBy(
                List.of(compared(0, Rel.GE, A), compared(-10, Rel.LE, A)), declared());
        TakenConstraint awayFromThree = new TakenConstraint.AwayFrom(A,
                new Count(BigDecimal.valueOf(3)));
        Reachability.Reaching.NarrowedPast past = Reachability.Reaching.narrowedPast(upToTen,
                ofTheRun(List.of(awayFromThree), List.of()));
        assertEquals(List.of(awayFromThree), past.narrowing(), "taken in");
        assertFalse(holds(past.narrowed(), 3, 0), "and the value is out of the region");
        assertTrue(holds(past.narrowed(), 4, 0));
    }

    @Test
    void aRunThatLeavesTheRegionNoRowWhenTakenInWholeIsSaidToLeaveNone() {
        SearchRegion declared = declared();
        Random random = new Random(3069);
        int empty = 0;
        for (int drawn = 0; drawn < 300; drawn++) {
            SearchRegion region = TakenConstraint.narrowedBy(some(random, 0, 4), declared);
            DemandReading.Answered run = ofTheRun(some(random, 1, 5), some(random, 0, 2));
            if (region.emptiness().isPresent() || TakenConstraint.narrowedBy(run.narrowing(),
                    region).emptiness().isEmpty()) {
                continue;
            }
            empty++;
            assertTrue(Reachability.Reaching.narrowedPast(region, run).leavesNone(),
                    () -> "taken in whole, " + run.narrowing() + " leaves no row of a region it"
                            + " is asked of, and what it is narrowed by leaves none either");
        }
        assertTrue(empty > 0, "some run drawn leaves no row, or nothing was asked");
    }

    /** A constraint drawn, with what it says of a row of the two numbers. */
    private record Drawn(TakenConstraint constraint, BiPredicate<Integer, Integer> holds) {}

    /** How far from nought a constant of a constraint drawn is, and a hole is put. */
    private static final int REACH = 3;

    /**
     * How far from nought a row is asked: a step past every corner two constraints drawn meet at,
     * which is no farther than a constant from one number and another from their sum.
     */
    private static final int ASKED_TO = 2 * REACH + 1;

    /**
     * A comparison of one of the numbers, their sum or their difference with a constant, or one
     * of the numbers held away from a value.
     */
    private static Drawn aDrawn(Random random) {
        int kind = random.nextInt(5);
        int constant = random.nextInt(2 * REACH + 1) - REACH;
        if (kind == 4) {
            boolean ofA = random.nextBoolean();
            return new Drawn(new TakenConstraint.AwayFrom(ofA ? A : D,
                    new Count(BigDecimal.valueOf(constant))),
                    (a, d) -> (ofA ? a : d) != constant);
        }
        Rel rel = RELS[random.nextInt(RELS.length)];
        Map<NumericTerm, ExactRatio> coefs = new LinkedHashMap<>();
        BiFunction<Integer, Integer, Integer> value = switch (kind) {
            case 0 -> {
                coefs.put(A, ExactRatio.ONE);
                yield (a, d) -> a;
            }
            case 1 -> {
                coefs.put(D, ExactRatio.ONE);
                yield (a, d) -> d;
            }
            case 2 -> {
                coefs.put(A, ExactRatio.ONE);
                coefs.put(D, ExactRatio.ONE);
                yield Integer::sum;
            }
            default -> {
                coefs.put(A, ExactRatio.ONE);
                coefs.put(D, ExactRatio.of(-1));
                yield (a, d) -> a - d;
            }
        };
        return new Drawn(new TakenConstraint.Affine(
                new LinearForm<>(ExactRatio.of(constant), coefs), rel),
                (a, d) -> rel.holds(Integer.signum(constant + value.apply(a, d))));
    }

    private static List<Drawn> drawn(Random random, int least, int most) {
        List<Drawn> out = new ArrayList<>();
        for (int at = 0, n = least + random.nextInt(most - least + 1); at < n; at++) {
            out.add(aDrawn(random));
        }
        return out;
    }

    private static List<TakenConstraint> constraintsOf(List<Drawn> drawn) {
        return drawn.stream().map(Drawn::constraint).toList();
    }

    /** Whether the row {@code a}, {@code d} is one {@code region} holds. */
    private static boolean holds(SearchRegion region, int a, int d) {
        return region.given(Map.of(A, new Count(BigDecimal.valueOf(a)),
                D, new Count(BigDecimal.valueOf(d)))).emptiness().isEmpty();
    }

    /**
     * The region what a run got past leaves holds, row by row, the rows the region holds that
     * meet every constraint of the run, in whatever order the run took them in: a constraint left
     * out is one every row of the region meets. Asked of regions with rows in them, of runs some
     * of whose constraints the region is shown to hold, and of holes, which narrow no run and
     * take a value out of it.
     */
    @Test
    void whatIsLeftOutIsWhatEveryRowOfTheRegionMeetsInEveryOrder() {
        SearchRegion declared = declared();
        Random random = new Random(3069);
        int asked = 0;
        int leftOut = 0;
        int held = 0;
        while (asked < 12) {
            List<Drawn> ofTheRegion = drawn(random, 1, 3);
            SearchRegion region = TakenConstraint.narrowedBy(constraintsOf(ofTheRegion), declared);
            if (region.emptiness().isPresent()) {
                continue;
            }
            asked++;
            List<Drawn> onTheWay = drawn(random, 1, 4);
            List<Drawn> ofTheRelation = drawn(random, 0, 1);
            List<Drawn> reversed = new ArrayList<>(onTheWay.reversed());
            List<Drawn> shuffled = new ArrayList<>(onTheWay);
            Collections.shuffle(shuffled, random);
            for (List<Drawn> order : List.of(onTheWay, reversed, shuffled)) {
                DemandReading.Answered run = ofTheRun(constraintsOf(order),
                        constraintsOf(ofTheRelation));
                Reachability.Reaching.NarrowedPast past =
                        Reachability.Reaching.narrowedPast(region, run);
                if (past.narrowing().size() < order.size() + ofTheRelation.size()) {
                    leftOut++;
                }
                for (int a = -ASKED_TO; a <= ASKED_TO; a++) {
                    for (int d = -ASKED_TO; d <= ASKED_TO; d++) {
                        int x = a;
                        int y = d;
                        boolean meetsAll = Stream.of(ofTheRegion, order, ofTheRelation)
                                .flatMap(List::stream)
                                .allMatch(each -> each.holds().test(x, y));
                        held += meetsAll ? 1 : 0;
                        assertEquals(meetsAll, holds(past.narrowed(), a, d),
                                () -> "the row " + x + ", " + y + " of " + constraintsOf(ofTheRegion)
                                        + " past " + run.narrowing() + ", left with "
                                        + past.narrowing());
                    }
                }
            }
        }
        assertTrue(leftOut > 0, "some constraint the region holds was left out");
        assertTrue(held > 0, "some row is left");
    }
}
