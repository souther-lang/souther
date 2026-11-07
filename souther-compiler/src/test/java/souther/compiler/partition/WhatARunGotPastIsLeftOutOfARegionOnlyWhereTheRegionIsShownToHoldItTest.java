package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.RuleReadings;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.SearchRegion;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;
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
 * at random from comparisons of two numbers and of their sum and difference.
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
        Compilation compilation = Compilation.ofSource("""
                module m

                data R = { a: Int, d: Int }
                data Yes

                behavior f : (r: R) -> Yes
                let f (r) = Yes
                """, "Main");
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

    @Test
    void aRunThatLeavesTheRegionNoRowWhenTakenInWholeIsSaidToLeaveNone() {
        SearchRegion declared = declared();
        Random random = new Random(3069);
        int empty = 0;
        for (int drawn = 0; drawn < 1000; drawn++) {
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
}
