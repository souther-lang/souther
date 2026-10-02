package souther.compiler.query;

import org.junit.jupiter.api.Test;
import souther.compiler.check.InvariantChecker;
import souther.compiler.check.TypeCardinality;
import souther.compiler.meta.ModulePath;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A ring of names each worn over the next, with nothing at the bottom, is found to be at fault by
 * supposing each name in turn has a value — and each supposing is paid for as a chain, not as the
 * ring again.
 *
 * <p>Two places the ring could come back. With one name supposed to have a value, nothing is read
 * through it, so the rest are a chain answered one link at a time; answered as the ring they were,
 * every link opens the names beneath it down to the supposed one, and the search opens the ring once
 * per name per name. And the rules of each link are read under the supposing: read afresh for each
 * question at each link, each reading walks the chain down to the supposed name, where a name that
 * writes nothing is read as the one beneath it and the chain is read once.
 *
 * <p>Held by how the counts grow, because that is what the two places change. The search asks once
 * per name, so a ring twice as long is asked about twice as often; a supposing answered as a chain
 * opens each link once and reads the chain once, so what each asking costs grows with the ring for
 * the names opened and not at all for the readings.
 */
class WhichNamesOfARingAreAtFaultIsAskedAtTheCostOfTheRingTest {

    /** Halved twice below, so a multiple of four. */
    private static final int RING = 80;

    /** {@code T1} to {@code T<names>}, each worn over the one before and the first over the last. */
    private static String ring(int names) {
        StringBuilder src = new StringBuilder("module chain\n\ndata T1 = T" + names + "\n");
        for (int i = 2; i <= names; i++) {
            src.append("data T").append(i).append(" = T").append(i - 1).append('\n');
        }
        return src.toString();
    }

    /** What compiling a ring of {@code names} cost: the names opened and the readings made. */
    private static long[] cost(int names) {
        long opened = TypeCardinality.namesOpened();
        long read = InvariantChecker.readingsMade();
        Compilation c = Compilation.ofDocuments(
                new LinkedHashMap<>(Map.of("chain.sou", ring(names))), Set.of(),
                ModulePath.EMPTY);
        c.answerEverything();
        List<String> said = c.db().allReports().stream()
                .map(each -> each.report().diagnostic().code().toString()).toList();
        assertEquals(1, said.size(), () -> "the ring is reported once and only once: " + said);
        return new long[] {TypeCardinality.namesOpened() - opened,
                InvariantChecker.readingsMade() - read};
    }

    @Test
    void aRingTwiceAsLongOpensNamesAsASquareAndMakesReadingsAsTheRing() {
        long[] quarter = cost(RING / 4);
        long[] half = cost(RING / 2);
        long[] whole = cost(RING);
        long shorterOpened = half[0] - quarter[0];
        long longerOpened = whole[0] - half[0];
        long shorterRead = half[1] - quarter[1];
        long longerRead = whole[1] - half[1];

        assertTrue(shorterOpened > 0 && shorterRead > 0,
                "a ring opened no name or made no reading, so this measures nothing");
        // Between the two growths each could have, since what is counted has lower terms beside
        // the one that grows: four times for a square and eight for a cube, twice for the ring and
        // four times for its square.
        assertTrue(longerOpened < 6 * shorterOpened,
                () -> "the names opened grow with the cube of the ring: "
                        + shorterOpened + " then " + longerOpened);
        assertTrue(longerRead < 3 * shorterRead,
                () -> "the readings made grow with the square of the ring: "
                        + shorterRead + " then " + longerRead);
    }
}
