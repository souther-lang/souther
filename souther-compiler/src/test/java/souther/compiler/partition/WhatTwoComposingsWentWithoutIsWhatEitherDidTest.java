package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.meaning.WhyNotTaken;

import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * What two composings of one way went without, between them, is what either went without.
 *
 * <p>An answer made of several composings is weaker for every condition any of them could not
 * compose against. One composing's account in place of the rest leaves out what the others went
 * without, and which one stood for the rest would follow the order they were made in.
 */
class WhatTwoComposingsWentWithoutIsWhatEitherDidTest {

    /** A condition either could not compose against is kept, once. */
    @Test
    void whatEitherCouldNotComposeAgainstIsKept() {
        CompositionAccount one = CompositionAccount.ofTheInput(List.of(gap(0)));
        CompositionAccount other = CompositionAccount.ofTheInput(List.of(gap(1), gap(0)));

        assertEquals(List.of(gap(0), gap(1)), one.alongside(other).onTheWay(),
                "both conditions were gone without, and the one both went without is one");
        assertEquals(Set.copyOf(one.alongside(other).onTheWay()),
                Set.copyOf(other.alongside(one).onTheWay()),
                "whichever composing was made first");
    }

    /**
     * A condition is taken up by an answer only where both took it up.
     *
     * <p>Where one of them did not, that composing went without it — and reconciled against the
     * way it is a gap. Taken up because the other took it up, the answer would be said to have
     * gone without less than one of its composings did.
     */
    @Test
    void aConditionIsTakenUpOnlyWhereBothTookItUp() {
        ConditionOccurrence both = condition(0);
        ConditionOccurrence onlyOne = condition(1);
        CompositionAccount one = new CompositionAccount(List.of(), List.of(),
                Set.of(both, onlyOne));
        CompositionAccount other = new CompositionAccount(List.of(), List.of(), Set.of(both));

        assertEquals(Set.of(both), one.alongside(other).takenUpByAnAnswer(),
                "the other composing went without what only the first took up");
        assertEquals(one.alongside(other).takenUpByAnAnswer(),
                other.alongside(one).takenUpByAnAnswer(),
                "whichever composing was made first");
    }

    private static ReachabilityGap gap(int which) {
        return new ReachabilityGap.Unstated(new OnTheWay.Declined(condition(which),
                new ConditionReportAnchor.WhereTheReadingMetIt("example.ruled", condition(which)),
                new WhyNotTaken.OutsideDomain(WhyNotTaken.DomainLimit.A_QUANTITY_ON_NO_ORDER)));
    }

    private static ConditionOccurrence condition(int which) {
        return new ConditionOccurrence("f", ConditionOccurrence.Reading.DECIDING, which);
    }
}
