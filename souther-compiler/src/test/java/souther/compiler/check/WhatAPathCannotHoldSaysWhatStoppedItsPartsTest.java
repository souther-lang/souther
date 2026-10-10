package souther.compiler.check;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.meaning.WhyUnread;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;

/**
 * A condition a path cannot hold says why, and says what stopped the meaning of every part under
 * it besides.
 *
 * <p>A path knows facts that all hold, so one of several things, one statement on each application
 * of a closure and some element meeting something are declined whole. That is the path's limit; a
 * part under it whose meaning went unread is the reading's, and an author who widened the path
 * would still meet it. Held over statements with nothing a path would take in, so no tree, binding
 * or position is asked about and none is handed in.
 */
class WhatAPathCannotHoldSaysWhatStoppedItsPartsTest {

    private static final WhyUnread NO_SIZE = new WhyUnread.NoMeasureOfItsSize();
    private static final WhyUnread NOT_LINEAR = new WhyUnread.OutsideTheLinearFragment(
            NonAffineOperation.PRODUCT_OF_NON_CONSTANT_VALUES);
    private static final WhyNotTaken NO_ALTERNATIVES =
            new WhyNotTaken.OutsideDomain(WhyNotTaken.DomainLimit.A_PATH_KNOWS_NO_ALTERNATIVES);

    private static final WhyNotTaken ELEMENT_FACTS_AS_WRITTEN = new WhyNotTaken.OutsideDomain(
            WhyNotTaken.DomainLimit.A_PATH_HOLDS_ELEMENT_FACTS_AS_WRITTEN);

    private static Proposition unread(int ordinal, WhyUnread why) {
        return new Proposition.Unread(Optional.empty(), ordinal, why, false, true);
    }

    private static List<WhyNotTaken> notTaken(Proposition stated, boolean positive) {
        Predicates.Assumed assumed = MeaningAssumptions.assumed(stated, positive, Known.top(), null,
                MeaningAssumptions.InputPlaces.NONE, null);
        assertFalse(assumed.shapeRead(), () -> stated.key() + " is not read to the end");
        return assumed.notTaken();
    }

    @Test
    void everyShapeDeclinedWholeSaysWhatStoppedItsParts() {
        Proposition first = unread(0, NO_SIZE);
        Proposition second = unread(1, NOT_LINEAR);
        List<Proposition> declined = List.of(
                new Proposition.Any(List.of(first, second)),
                new Proposition.OnAnApplication(List.of(first, second)),
                new Proposition.Some(TermPath.of("xs"), new Proposition.All(List.of(first, second)),
                        true));
        for (Proposition stated : declined) {
            for (boolean positive : List.of(true, false)) {
                Proposition asked = positive ? stated : stated.denied();
                // A denied disjunction is a conjunction, which a path takes part by part; and no
                // element meeting something is what every element meets, which a path holds only
                // as the closure it was written with.
                WhyNotTaken whole = asked instanceof Proposition.Some some && !some.holds()
                        ? ELEMENT_FACTS_AS_WRITTEN : NO_ALTERNATIVES;
                List<WhyNotTaken> expected = asked instanceof Proposition.All
                        ? List.of(new WhyNotTaken.MeaningUnread(NO_SIZE),
                                new WhyNotTaken.MeaningUnread(NOT_LINEAR))
                        : List.of(whole, new WhyNotTaken.MeaningUnread(NO_SIZE),
                                new WhyNotTaken.MeaningUnread(NOT_LINEAR));
                assertEquals(expected, notTaken(stated, positive),
                        stated.key() + " coming out " + positive);
            }
        }
    }
}
