package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.math.BigDecimal;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a target's own rules leave it is kept when a condition over a form is asked of it too, and
 * the condition is what says the walk is not the whole question.
 *
 * <p>Two things a caller holds and neither stands for the other. A rule about the position says
 * which numbers it may take; a rule about a form of it and another says nothing about this one on
 * its own, because which numbers it leaves here is whatever the other position took. Kept as one,
 * the second takes the first away — and a search of a bounded position then looks over the whole
 * order, which is the walk this compiler pays for twice and the values it offers a reader outside
 * what the rules allow.
 *
 * <p>The other direction is what a word about the model rests on: a target under a condition over a
 * form has not been walked whole however far its own run was walked.
 */
class WhatIsKnownOfATargetSurvivesAConditionOverAFormTest {

    private static final Carrier DECIMALS = new Carrier.Dense();

    private static final TakenConstraint.Affine OVER_A_FORM = new TakenConstraint.Affine(
            LinearForm.<NumericTerm>atom(new NumericTerm.ValueOf(TermPath.of("r").then("cost")))
                    .plus(LinearForm.atom(new NumericTerm.ValueOf(TermPath.of("r").then("paid")))),
            Rel.GE);

    private static final TakenConstraint.Affine OVER_ANOTHER_FORM = new TakenConstraint.Affine(
            LinearForm.<NumericTerm>atom(new NumericTerm.ValueOf(TermPath.of("r").then("cost")))
                    .plus(LinearForm.atom(new NumericTerm.ValueOf(TermPath.of("r").then("owed")))),
            Rel.GE);

    private static Level at(String value) {
        return new Level.OnACarrier(DECIMALS, new Count(new BigDecimal(value)));
    }

    private static LevelRegion from(String low, String high) {
        return LevelRegion.of(new LevelInterval(Bound.at(at(low), true), Bound.at(at(high), true)));
    }

    /** A question about the target alone is walked whole, and one over a form is not. */
    @Test
    void aConditionOverAFormIsWhatSaysTheWalkIsNotTheWholeQuestion() {
        assertTrue(NumbersAskedFor.of(from("0", "10")).isWalkedWhole(),
                "what a rule leaves the target is every number it may take");
        assertFalse(NumbersAskedFor.onlyTogether(OVER_A_FORM).isWalkedWhole(),
                "and a condition over a form leaves that to what the other position took");
        assertTrue(NumbersAskedFor.ANYTHING.isWalkedWhole(),
                "a target under no condition at all is walked whole by walking its order");
    }

    /** A condition over a form leaves the target every number, which is not nothing known. */
    @Test
    void aConditionOverAFormLeavesTheTargetItsWholeOrder() {
        NumbersAskedFor asked = NumbersAskedFor.onlyTogether(OVER_A_FORM);

        assertEquals(LevelRegion.EVERYTHING.parts(), asked.values().parts(),
                "nothing of the order is taken away by a condition that is not about it");
        assertEquals(List.of(OVER_A_FORM), asked.onlyTogether(),
                "and the condition itself is carried, because it is what is known");
    }

    /**
     * Crossing the two keeps both halves.
     *
     * <p>Which is the case a position under its own rule and a form's is asked in, and the one a
     * single arm for "this is joint" would lose: the run would go, and the search would look over
     * the whole order for a position the rules bound.
     */
    @Test
    void crossingKeepsWhatIsKnownAndWhyItIsNotTheWholeQuestion() {
        NumbersAskedFor both = NumbersAskedFor.of(from("0", "10"))
                .meet(NumbersAskedFor.onlyTogether(OVER_A_FORM));

        assertTrue(both.values().contains(at("5")), "what the target's own rule leaves is kept");
        assertFalse(both.values().contains(at("11")),
                "and what it does not leave is still out of the question");
        assertEquals(List.of(OVER_A_FORM), both.onlyTogether(),
                "with the condition over the form saying the walk is not the whole of it");
        assertFalse(both.isWalkedWhole(),
                "so a walk of the run is not a walk of everything asked");
    }

    /** Crossing the other way round answers the same, since a crossing is about both sides. */
    @Test
    void crossingIsTheSameWhicheverSideIsAsked() {
        NumbersAskedFor one = NumbersAskedFor.of(from("0", "10"))
                .meet(NumbersAskedFor.onlyTogether(OVER_A_FORM));
        NumbersAskedFor other = NumbersAskedFor.onlyTogether(OVER_A_FORM)
                .meet(NumbersAskedFor.of(from("0", "10")));

        assertEquals(one.onlyTogether(), other.onlyTogether(),
                "the same conditions are carried either way round");
        for (String value : List.of("0", "5", "10", "11")) {
            assertEquals(one.values().contains(at(value)), other.values().contains(at(value)),
                    () -> "and the same values are left at " + value);
        }
    }

    /** Two rules about the target alone leave what both of them leave, and are walked whole. */
    @Test
    void twoRulesAboutTheTargetAreCrossed() {
        NumbersAskedFor both = NumbersAskedFor.of(from("0", "10"))
                .meet(NumbersAskedFor.of(from("5", "20")));

        assertTrue(both.values().contains(at("7")), "what both leave is left");
        assertFalse(both.values().contains(at("2")), "what only one of them leaves is not");
        assertTrue(both.isWalkedWhole(),
                "and nothing about a form is in the way of walking it whole");
    }

    /** Conditions over two forms are both carried, because either may be why a value is refused. */
    @Test
    void everyConditionOverAFormIsCarried() {
        NumbersAskedFor both = NumbersAskedFor.onlyTogether(OVER_A_FORM)
                .meet(NumbersAskedFor.onlyTogether(OVER_ANOTHER_FORM));

        assertEquals(List.of(OVER_A_FORM, OVER_ANOTHER_FORM), both.onlyTogether(),
                "both conditions are what is known of the target");
    }

    /** One condition asked twice is one condition, not a second thing standing in the way. */
    @Test
    void oneConditionAskedTwiceIsOneCondition() {
        NumbersAskedFor both = NumbersAskedFor.onlyTogether(OVER_A_FORM)
                .meet(NumbersAskedFor.onlyTogether(OVER_A_FORM));

        assertEquals(List.of(OVER_A_FORM), both.onlyTogether(),
                "the same condition met twice is the one condition");
    }

    /**
     * One number is the whole of what a search asked for it can try, and a class is not.
     *
     * <p>What licenses one candidate standing for the whole question. A run holding one value is
     * that value; a run holding more is a class, and a search that tried a number out of it has
     * tried a number out of it.
     */
    @Test
    void oneNumberIsWhatOneCandidateIsTheWholeOf() {
        assertTrue(NumbersAskedFor.of(LevelRegion.point(at("5"))).isOneNumber(),
                "a rule leaving one number leaves one number");
        assertFalse(NumbersAskedFor.of(from("0", "10")).isOneNumber(),
                "and a run holding more than one does not");
        assertFalse(NumbersAskedFor.of(LevelRegion.EVERYTHING).isOneNumber(),
                "neither does the whole order");
    }

    /**
     * A target left one number by its own rule and under a condition over a form is not one
     * number a candidate is the whole of.
     *
     * <p>The rule's number may be refused by what the other position took, and nothing here looked.
     * Read off the run alone, the one candidate tried would carry a word about the model.
     */
    @Test
    void oneNumberUnderAConditionOverAFormIsNotWalkedWholeByTryingIt() {
        NumbersAskedFor asked = NumbersAskedFor.of(LevelRegion.point(at("5")))
                .meet(NumbersAskedFor.onlyTogether(OVER_A_FORM));

        assertTrue(asked.values().parts().getFirst().onePlace(),
                "the values left are one place on the order");
        assertFalse(asked.isOneNumber(),
                "and trying it is still not trying the whole of what was asked");
    }
}
