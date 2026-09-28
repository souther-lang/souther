package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.types.ConstructOccurrence;
import souther.compiler.types.ModelOccurrence;

import java.util.ArrayList;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * What a reading recorded on the way to each comparison a body writes, for a test that wants all of
 * them.
 *
 * <p>Asked of each comparison the body writes, by the place the model states it at, and answered
 * the way a border reads it ({@link ReachingCuts#wayTo}). What a reading kept is a lookup by
 * comparison and offers no walk over what it holds, so a test that wants every account names the
 * comparisons itself: the body is where they are written, and it says them in the order it writes
 * them.
 *
 * <p>Only the accounts that say something. The question a border asks cannot tell a comparison the
 * reading collected nothing at from one it recorded an empty account for, and a body may write a
 * comparison the reading never reached, so an empty answer is not an observation of the reading.
 */
final class ReachingAccounts {

    private ReachingAccounts() {
    }

    /** The account on the way to each comparison {@code body} writes that has one, in the order
     *  the body writes them. */
    static List<List<OnTheWay>> filedFor(ReachingCuts reaching, Core body) {
        List<List<OnTheWay>> ways = new ArrayList<>();
        for (ConstructOccurrence written : comparisonsIn(body)) {
            ModelOccurrence.statedAt(written).ifPresent(stated -> {
                List<OnTheWay> account = reaching.wayTo(stated).onTheWay();
                if (!account.isEmpty()) {
                    ways.add(account);
                }
            });
        }
        return List.copyOf(ways);
    }

    private static Set<ConstructOccurrence> comparisonsIn(Core body) {
        Set<ConstructOccurrence> out = new LinkedHashSet<>();
        collect(body, out);
        return out;
    }

    private static void collect(Core e, Set<ConstructOccurrence> out) {
        if (e instanceof Core.Binary binary && binary.origin() != null
                && binary.origin().isWritten()) {
            out.add(binary.occurrence());
        }
        Core.forEachChild(e, child -> collect(child, out));
    }
}
