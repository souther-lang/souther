package souther.compiler.partition;

import souther.compiler.inputs.BlockedDescent;
import souther.compiler.inputs.Position;
import souther.compiler.inputs.RulesLeftUnread;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.Set;

/**
 * What a reading of one position left behind that no later phase can take away.
 *
 * <p><b>Two facts with one lifetime, held together so that one cannot be carried without the
 * other.</b> What a position is measured at is rebuilt as a body's rules are read
 * ({@link PositionMeasurements#measuredAt}), which is a place a caller writes the parts out by
 * hand. A position whose elements could not be reached once came back from the second phase with
 * nothing to say it had ever stopped, because one such rebuild did not name the field. Written as
 * one value, a rebuild names it or does not compile.
 *
 * <p><b>Not what the position is still waiting on.</b> {@link PositionAccount#pending} is a
 * fallback: it is what a position is left with <em>if nothing else answers for it</em>, and it is
 * gone the moment something does. These two are observations, and they stay true whatever answers
 * later — a
 * {@code Map} nothing can be read into is one nothing was read into however plainly a rule about its
 * size divides it. Holding the three in one value would put a phase-local state and two settled
 * facts under one lifetime, which is the merge issue #1084 is about, one level up.
 *
 * @param blockedDescent that the walk could not go into what the position holds, or null where it
 *                       did
 * @param rulesLeftUnread why the rules the position was owed went unread, empty where they were all
 *                       reached
 */
public record ReadingResidue(BlockedDescent blockedDescent,
                             Set<RulesLeftUnread> rulesLeftUnread) {

    /** A reading that got to the end of everything it was owed. */
    public static final ReadingResidue NOTHING = new ReadingResidue(null, Set.of());

    public ReadingResidue {
        rulesLeftUnread = Collections.unmodifiableSet(new LinkedHashSet<>(rulesLeftUnread));
        // What the arms say about themselves, held to — the same agreement the reader that settled
        // them held, asked the same way ({@link RulesLeftUnread.HandoffUnread#namesABlockedDescent}).
        // An arm naming a descent this does not carry would fold into a finding nothing writes and
        // the stop would go unsaid; an arm denying one beside a descent that is reported puts the
        // stop out twice. Both are a copy that dropped one of the pair, and this is where a copy is
        // caught.
        for (RulesLeftUnread each : rulesLeftUnread) {
            if (each instanceof RulesLeftUnread.Handoff handoff
                    && handoff.why().namesABlockedDescent() != (blockedDescent != null)) {
                throw new IllegalArgumentException(
                        "a handing over and the descent beside it disagree: " + handoff.why()
                                + " with " + blockedDescent);
            }
        }
    }

    /** What one position's reading came to, as the reading itself answered it. */
    public static ReadingResidue of(Position position) {
        return new ReadingResidue(BlockedDescent.of(position.structure()),
                position.rulesLeftUnread());
    }
}
