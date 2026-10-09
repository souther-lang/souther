package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.flow.AWayThrough;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.WhyNotTaken;
import souther.compiler.meaning.WhyUnread;

import java.util.List;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * What the rules leave behind a way is an upper bound, so only a proof rules a way out — and a way
 * that is not ruled out says which parts of the statement were never asked of the rules.
 *
 * <p>Held over statements with no relation in them, so the rules are never asked anything and are
 * not handed in: what is under test is how parts nothing read are carried, and a relation would put
 * a second question beside that one.
 */
class AWayNotRuledOutIsNeverAProofTest {

    private static final WhyUnread NO_SIZE = new WhyUnread.NoMeasureOfItsSize();
    private static final WhyUnread NOT_LINEAR = new WhyUnread.OutsideTheLinearFragment();

    private static Proposition unread(int ordinal, WhyUnread why) {
        return new Proposition.Unread(Optional.empty(), ordinal, why, false, true);
    }

    private static AWayThrough admits(Proposition stated, boolean want) {
        return WhatTheRulesLeave.admits(stated, want, null);
    }

    private static List<WhyNotTaken> notAsked(AWayThrough way) {
        return assertInstanceOf(AWayThrough.NotRuledOut.class, way).notAsked();
    }

    /** A part nothing read rules out neither way, and says why it was not asked. */
    @Test
    void aPartNothingReadRulesOutNeitherWay() {
        for (boolean want : List.of(true, false)) {
            assertEquals(List.of(new WhyNotTaken.MeaningUnread(NO_SIZE)),
                    notAsked(admits(unread(0, NO_SIZE), want)), "wanting " + want);
        }
    }

    /**
     * Either of two parts, one of which never holds and one nothing read: the only way through is
     * the part nothing read, and that is not a proof that no run takes it.
     */
    @Test
    void aDisjunctionLeftOnlyToAnUnreadPartIsNotRuledOut() {
        Proposition either = new Proposition.Any(List.of(new Proposition.Always(false),
                unread(0, NO_SIZE)));

        assertEquals(List.of(new WhyNotTaken.MeaningUnread(NO_SIZE)),
                notAsked(admits(either, true)));
    }

    /** A conjunction with a part that never holds is ruled out, whatever else is in it: that is a
     *  proof, and the part nothing read does not weaken it. */
    @Test
    void aConjunctionWithAPartThatNeverHoldsIsRuledOut() {
        Proposition both = new Proposition.All(List.of(unread(0, NO_SIZE),
                new Proposition.Always(false)));

        assertInstanceOf(AWayThrough.RuledOut.class, admits(both, true));
    }

    /** Every part nothing read keeps its own reason, once each, in the order they stand. */
    @Test
    void everyUnreadPartKeepsItsReason() {
        Proposition both = new Proposition.All(List.of(unread(0, NO_SIZE),
                unread(1, NOT_LINEAR), unread(2, NO_SIZE)));

        assertEquals(List.of(new WhyNotTaken.MeaningUnread(NO_SIZE),
                        new WhyNotTaken.MeaningUnread(NOT_LINEAR)),
                notAsked(admits(both, true)));
        assertEquals(List.of(new WhyNotTaken.MeaningUnread(NO_SIZE),
                        new WhyNotTaken.MeaningUnread(NOT_LINEAR)),
                notAsked(admits(both, false)), "and failing, each part is a way it can fail");
    }
}
