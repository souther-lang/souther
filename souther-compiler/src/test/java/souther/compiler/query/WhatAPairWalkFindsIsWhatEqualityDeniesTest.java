package souther.compiler.query;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Random;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * A walk of two answers finds something exactly where equality denies what the shapes say.
 *
 * <p>The promise, said once, against graphs nobody chose. Two things built from one recipe are one
 * thing; whether they say so is {@code equals}'s answer, and where the two disagree is what this
 * walk is for. So:
 *
 * <pre>a.equals(b) ⟺ the walk finds nothing</pre>
 *
 * <p>Both directions matter and they fail differently. A walk that finds something where equality
 * agrees names a defect that is not there and sends a reader after the compiler; a walk that finds
 * nothing where equality denies leaves a defect in an answer with every check green. Every finding
 * three rounds of review turned up was one of those two, and each was met with a fixture for the
 * case that had been missed — by whoever had already missed it.
 *
 * <p>Which is what this is for and what the fixtures beside it are not. {@link
 * APairWalkNamesADefectWhereItIsTest} says what each shape comes to, in words, at a place a reader
 * can go and look; this says the mechanism is right about shapes nobody wrote down. Neither does the
 * other's work: a property with no examples is a failure with nowhere to start, and examples with no
 * property are a list of what somebody thought of.
 *
 * <p>A pair the walk could not cover is not held to this. It is held to saying so, which is what the
 * arm it comes back on is.
 */
class WhatAPairWalkFindsIsWhatEqualityDeniesTest {

    /** Enough shapes to reach every way the walk takes something apart, and small enough that a
     *  failure is a graph somebody can read. */
    private static final int HOW_MANY = 2_000;

    private static final int HOW_DEEP = 4;

    /** Fixed, so a failure is a graph that can be got back. */
    private static final long SEED = 1103;

    @Test
    void aWalkFindsSomethingExactlyWhereEqualityDeniesTheShape() {
        Random random = new Random(SEED);
        List<String> wrong = new ArrayList<>();
        for (int i = 0; i < HOW_MANY; i++) {
            AGraphNobodyChose.Recipe recipe = AGraphNobodyChose.recipe(random, HOW_DEEP);
            Object one = AGraphNobodyChose.built(recipe, random);
            Object other = AGraphNobodyChose.built(recipe, random);
            if (AGraphNobodyChose.holdsSomethingWithNoRule(recipe)) {
                continue;
            }
            int denials = AGraphNobodyChose.denialsIn(recipe, one, other);
            switch (Divergence.between(one, other)) {
                case Covered.Whole<Divergence>(List<Divergence> found) -> {
                    // Two graphs of one shape are one thing, so nothing in them says two different
                    // things and every denial in them is one of these.
                    List<Divergence> otherwise = found.stream()
                            .filter(each -> each.kind() != Divergence.Kind.THE_SAME_THING_TWICE).toList();
                    if (!otherwise.isEmpty()) {
                        wrong.add("said " + otherwise + " of two graphs of one shape, in " + recipe);
                    }
                    if (found.size() != denials) {
                        wrong.add("found " + found.size() + " where " + denials
                                + " things deny being what they are, in " + recipe + ": " + found);
                    }
                }
                // A walk that fell short is held to having said so and to nothing else: what it did
                // not look at is what it cannot be asked about.
                case Covered.Partly<Divergence> _ -> { }
            }
        }

        assertEquals(List.of(), wrong,
                "graphs where what the walk finds is not what equality denies");
    }

    /**
     * And the shapes reach the walk rather than sliding past it.
     *
     * <p>The control the property needs. Every graph agreeing with equality is what a walk that
     * looked at nothing would answer too, so the run has to reach both sides of the promise — graphs
     * the two agree on, and graphs where equality denies what the shape says.
     */
    @Test
    void theShapesReachBothSidesOfIt() {
        Random random = new Random(SEED);
        int agreed = 0;
        int denied = 0;
        for (int i = 0; i < HOW_MANY; i++) {
            AGraphNobodyChose.Recipe recipe = AGraphNobodyChose.recipe(random, HOW_DEEP);
            if (AGraphNobodyChose.built(recipe, random)
                    .equals(AGraphNobodyChose.built(recipe, random))) {
                agreed++;
            } else {
                denied++;
            }
        }

        int alike = agreed;
        int apart = denied;
        org.junit.jupiter.api.Assertions.assertTrue(alike > HOW_MANY / 10,
                () -> "only " + alike + " of " + HOW_MANY + " shapes come out equal");
        org.junit.jupiter.api.Assertions.assertTrue(apart > HOW_MANY / 10,
                () -> "only " + apart + " of " + HOW_MANY + " shapes come out unequal");
    }
}
