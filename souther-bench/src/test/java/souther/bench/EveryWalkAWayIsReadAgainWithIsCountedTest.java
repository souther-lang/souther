package souther.bench;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Every walk a way past the figure is read again with is counted against the walks it is read
 * again with ({@code CompositionBudget.WALKS_A_WAY_IS_READ_AGAIN_WITH}).
 *
 * <p>The bound is over the whole of the reading again, so it holds only while each walk goes
 * through the one place that counts it. A walk taken beside it — for a witness, for a way of
 * alternatives no row takes, or for what the way is read again as — is one more walk than the
 * figure says, and a reader told the walks ran out is told of a count that was not the one kept.
 * Read off the compiled classes: whatever in the reading again asks the way it was read from to
 * be read as something else is that place, and nothing else is.
 */
class EveryWalkAWayIsReadAgainWithIsCountedTest {

    private static final String READ_AGAIN = "souther.compiler.partition.AWayReadForARelation";

    private static final String READ_FROM = "souther.compiler.partition.Reachability$ReadFrom";

    @Test
    void onlyTheCountedWalkReadsTheWayAgain() {
        Set<String> walking = new LinkedHashSet<>();
        for (Compiled.Site site : Compiled.sites()) {
            if (site.owner().equals(READ_FROM) && site.member().equals("readAs")
                    && (site.from().equals(READ_AGAIN) || site.from().startsWith(READ_AGAIN + "$"))) {
                walking.add(site.at());
            }
        }
        assertEquals(List.of(READ_AGAIN + "#walked(Ljava/util/List;)"
                        + "Lsouther/compiler/partition/Reachability;"),
                List.copyOf(walking),
                "a way read again is walked somewhere its walks are not counted");
    }
}
