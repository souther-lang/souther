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
 * other.</b> An axis is rebuilt whenever a body's rules re-point it at another number
 * ({@link Axis#measuredAt}) or divide it ({@link Axis#carrying}), and each of those is a place a
 * caller writes the parts out by hand. A position whose elements could not be reached once came
 * back from the second phase with nothing to say it had ever stopped, because one such rebuild did
 * not name the field. Written as one value, a rebuild names it or does not compile.
 *
 * <p><b>Not what the position is still waiting on.</b> {@link Axis#pending} is a fallback: it is
 * what a position is left with <em>if nothing else answers for it</em>, and it is gone the moment
 * something does. These two are observations, and they stay true whatever answers later — a
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
        // What the arm says about itself, held to. `FromBlockedDescent` is the one arm whose finding
        // is somebody else's — the stop is reported as the blocked descent beside it, and this is
        // folded away — so an arm arriving without the descent it names would fold into a finding
        // nothing writes, and the stop would go unsaid. The producer proved the two agree
        // (`InputDomain`); this is where a copy that dropped one of them is caught.
        if (blockedDescent == null && rulesLeftUnread.stream().anyMatch(
                each -> each instanceof RulesLeftUnread.Handoff handoff
                        && handoff.why()
                                instanceof RulesLeftUnread.HandoffUnread.FromBlockedDescent)) {
            throw new IllegalArgumentException(
                    "a handing over left standing by a blocked descent, with no blocked descent: "
                            + rulesLeftUnread);
        }
    }

    /** What one position's reading came to, as the reading itself answered it. */
    public static ReadingResidue of(Position position) {
        return new ReadingResidue(BlockedDescent.of(position.structure()),
                position.rulesLeftUnread());
    }
}
