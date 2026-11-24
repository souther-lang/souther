package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.KeyedAccumulation;
import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * A name a counting walk's step binds to the value found under a key is given what the law says
 * of that value where it receives it, and nowhere else: under the part of the site that binds it,
 * in the step of the walk. Built by hand, since which node a reader meets where is what is held.
 *
 * <p>The seed and what is walked look for no site of this walk, nor does a part of the site other
 * than the one that binds the name, and a name once given keeps its range below.
 */
class WhatAStepsNameHoldsIsGivenWhereItIsBoundTest {

    private static final SourcePos POS = new SourcePos(1, 1);
    private static final BindingId FOUND =
            new BindingId(new BindingOwner.OfValue("model", "count"), 0);

    private static Core node(long n) {
        return new Core.Int(n, Type.INT, POS);
    }

    private final Core site = node(1);
    private final Core under = node(2);
    private final Core key = node(3);
    private final Core step = node(4);
    private final Core seed = node(5);

    private final KeyedAccumulation counted = new KeyedAccumulation(seed, null, key,
            new KeyedAccumulation.Filed.Counted(ExactRatio.ONE, ExactRatio.ONE), true,
            new KeyedAccumulation.Found(site, under, FOUND));

    private final Pullback.WhatTheStepsNamesHold inTheStep =
            Pullback.WhatTheStepsNamesHold.NOTHING.inTheWalk(step, counted, step);

    @Test
    void theNameIsGivenItsRangeUnderThePartThatBindsIt() {
        FormRange held = inTheStep.under(site, under).of(FOUND);
        assertNotNull(held);
        assertEquals(ExactRatio.ONE, held.least());
        assertNull(inTheStep.of(FOUND), "nothing is given before the site binds it");
    }

    @Test
    void anotherPartOfTheSiteGivesNothing() {
        assertNull(inTheStep.under(site, key).of(FOUND));
        assertNull(inTheStep.under(site, key).found(), "and looks for the site no further");
    }

    @Test
    void theSeedAndWhatIsWalkedLookForNoSite() {
        Pullback.WhatTheStepsNamesHold inTheSeed =
                Pullback.WhatTheStepsNamesHold.NOTHING.inTheWalk(step, counted, seed);
        assertNull(inTheSeed.found());
        assertNull(inTheSeed.under(site, under).of(FOUND));
    }

    @Test
    void aWalkInsideLooksForItsOwnSiteAndKeepsWhatIsGiven() {
        Pullback.WhatTheStepsNamesHold given = inTheStep.under(site, under);
        Pullback.WhatTheStepsNamesHold inside = given.inTheWalk(step, null, step);
        assertNull(inside.found());
        assertNotNull(inside.of(FOUND), "one binder binds the name, wherever it is read below");
    }

    @Test
    void aSiteMetBelowOtherNodesIsStillLookedFor() {
        assertEquals(inTheStep, inTheStep.under(key, seed));
    }
}
