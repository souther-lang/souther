package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.check.InvariantChecker;
import souther.compiler.check.TypeCardinality;
import souther.compiler.meta.ModulePath;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.IntFunction;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A ring of declarations with nothing at the bottom is found to be at fault by supposing each of them
 * in turn has a value — and each supposing is paid for as what is left of the ring once one name in
 * it reads nothing, not as the ring again.
 *
 * <p>Three places the ring could come back. With one name supposed to have a value, nothing is read
 * through it, so the rest are a chain answered one link at a time; answered as the ring they were,
 * every link opens the names beneath it down to the supposed one, and the search opens the ring once
 * per name per name. The rules of each link are read under the supposing, and where a rule is
 * written under the supposed name each reading stops there: read afresh for each link, a chain of
 * names that write nothing would be walked once per link, where each is read as the one beneath it
 * and the chain is read once. And where nothing is written under any name supposed, stopping there
 * reads what reading on would: every declaration is lent its own reading, made once whatever is
 * supposed, rather than read again under each supposing.
 *
 * <p>Held by how the counts grow, because that is what the three places change. The search asks once
 * per name, so a ring twice as long is asked about twice as often; a supposing answered as a chain
 * opens each link once and reads the chain once, so what each asking costs grows with the ring for
 * the names opened and not at all for the readings.
 */
class WhichNamesOfARingAreAtFaultIsAskedAtTheCostOfTheRingTest {

    /** Halved twice below, so a multiple of four. */
    private static final int RING = 80;

    /**
     * {@code T1}, a record holding the last of the ring and a number its rule bounds, and {@code T2}
     * to {@code T<names>}, each a name worn over the one before. A rule is under every name of it.
     */
    private static String namesOverARecordWithARule(int names) {
        StringBuilder src = new StringBuilder("module chain\n\ndata T1 = { p: T" + names
                + ", k: Int }\n    invariant k1 = k >= 0\n");
        for (int i = 2; i <= names; i++) {
            src.append("data T").append(i).append(" = T").append(i - 1).append('\n');
        }
        return src.toString();
    }

    /** {@code T1} to {@code T<names>}, each a record holding the one before and the first holding
     *  the last, and no rule anywhere. */
    private static String recordsWithNoRule(int names) {
        StringBuilder src = new StringBuilder("module chain\n\ndata T1 = { p: T" + names + " }\n");
        for (int i = 2; i <= names; i++) {
            src.append("data T").append(i).append(" = { p: T").append(i - 1).append(" }\n");
        }
        return src.toString();
    }

    /** What compiling a ring of {@code names} cost: the names opened and the readings made. */
    private static long[] cost(IntFunction<String> ring, int names) {
        long opened = TypeCardinality.namesOpened();
        long read = InvariantChecker.readingsMade();
        Compilation c = Compilation.ofDocuments(
                new LinkedHashMap<>(Map.of("chain.sou", ring.apply(names))), Set.of(),
                ModulePath.EMPTY);
        c.answerEverything();
        List<String> said = c.db().allReports().stream()
                .map(each -> each.report().diagnostic().code().toString()).toList();
        assertEquals(1, said.size(), () -> "the ring is reported once and only once: " + said);
        return new long[] {TypeCardinality.namesOpened() - opened,
                InvariantChecker.readingsMade() - read};
    }

    /** What a ring twice as long cost beyond one half as long, set beside the same for half. */
    private static long[][] growth(IntFunction<String> ring) {
        long[] quarter = cost(ring, RING / 4);
        long[] half = cost(ring, RING / 2);
        long[] whole = cost(ring, RING);
        return new long[][] {
                {half[0] - quarter[0], whole[0] - half[0]},
                {half[1] - quarter[1], whole[1] - half[1]}};
    }

    // Each bound is between the two growths what is counted could have, since it has lower terms
    // beside the one that grows: four times for a square and eight for a cube, twice for the ring
    // and four times for its square.

    @Test
    void namesOverARecordAreOpenedAsASquareAndReadAsTheRing() {
        long[][] grew = growth(WhichNamesOfARingAreAtFaultIsAskedAtTheCostOfTheRingTest
                ::namesOverARecordWithARule);
        long[] opened = grew[0];
        long[] read = grew[1];

        assertTrue(opened[0] > 0 && read[0] > 0,
                "a ring opened no name or made no reading, so this measures nothing");
        assertTrue(opened[1] < 6 * opened[0],
                () -> "the names opened grow with the cube of the ring: "
                        + opened[0] + " then " + opened[1]);
        assertTrue(read[1] < 3 * read[0],
                () -> "the readings made grow with the square of the ring: "
                        + read[0] + " then " + read[1]);
    }

    @Test
    void recordsWithNoRuleAreReadAsTheRing() {
        long[] read = growth(WhichNamesOfARingAreAtFaultIsAskedAtTheCostOfTheRingTest
                ::recordsWithNoRule)[1];

        assertTrue(read[0] > 0, "a ring made no reading, so this measures nothing");
        assertTrue(read[1] < 3 * read[0],
                () -> "the readings made grow with the square of the ring: "
                        + read[0] + " then " + read[1]);
    }
}
