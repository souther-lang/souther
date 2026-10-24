package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.Random;
import java.util.Set;
import java.util.TreeSet;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * The sharings of so many elements among kinds that are looked at are those that give a count
 * asked for of how many meet each statement, and every one of those — and the walk is held to a
 * figure however many kinds there are and however little of the sharing a count settles.
 */
class SharingsAmongKindsAreEveryOneThatCanGiveACountAskedForAndNoOtherTest {

    private static final int MOST = 8;

    /** Every way of sharing {@code size} elements out among {@code kinds} kinds. */
    private static void everySharing(int kinds, int size, List<int[]> into) {
        share(kinds, 0, size, new int[kinds], into);
    }

    private static void share(int kinds, int kind, int left, int[] counts, List<int[]> into) {
        if (kind == kinds - 1) {
            counts[kind] = left;
            into.add(counts.clone());
            return;
        }
        for (int count = 0; count <= left; count++) {
            counts[kind] = count;
            share(kinds, kind + 1, left - count, counts, into);
        }
    }

    /** Whether a sharing gives each count asked for, by the definition. */
    private static boolean givesACountAskedFor(int[] sharing, boolean[][] meets,
                                               boolean[][] asked, int kept) {
        for (int statement = 0; statement < asked.length; statement++) {
            int meeting = 0;
            for (int kind = 0; kind < sharing.length; kind++) {
                meeting += meets[kind][statement] ? sharing[kind] : 0;
            }
            boolean some = false;
            if (statement == kept) {
                for (int different = meeting > 0 ? 1 : 0; different <= meeting; different++) {
                    some |= asked[statement][different];
                }
            } else {
                some = asked[statement][meeting];
            }
            if (!some) {
                return false;
            }
        }
        return true;
    }

    private static String spelled(int[] sharing) {
        return Arrays.toString(sharing);
    }

    @Test
    void theSharingsLookedAtAreExactlyThoseThatGiveACountAskedFor() {
        Random random = new Random(20261025);
        int walked = 0;
        for (int round = 0; round < 3000; round++) {
            int kinds = 1 + random.nextInt(5);
            int statements = 1 + random.nextInt(3);
            boolean[][] meets = new boolean[kinds][statements];
            for (boolean[] each : meets) {
                for (int statement = 0; statement < statements; statement++) {
                    each[statement] = random.nextBoolean();
                }
            }
            boolean[][] asked = new boolean[statements][MOST + 1];
            for (boolean[] each : asked) {
                for (int count = 0; count <= MOST; count++) {
                    each[count] = random.nextInt(3) == 0;
                }
            }
            int kept = random.nextInt(3) == 0 ? random.nextInt(statements) : -1;
            for (int size = 0; size <= MOST; size++) {
                Set<String> expected = new TreeSet<>();
                List<int[]> all = new ArrayList<>();
                everySharing(kinds, size, all);
                for (int[] each : all) {
                    if (givesACountAskedFor(each, meets, asked, kept)) {
                        expected.add(spelled(each));
                    }
                }
                Set<String> looked = new TreeSet<>();
                SharingsAmongKinds sharings = new SharingsAmongKinds(meets, asked, kept, 1 << 20);
                assertTrue(sharings.ofSize(size, each -> looked.add(spelled(each))));
                assertEquals(expected, looked, "kinds " + Arrays.deepToString(meets)
                        + " asked " + Arrays.deepToString(asked) + " kept " + kept);
                walked += looked.size();
            }
        }
        assertTrue(walked > 2000, "sharings met: " + walked);
    }

    /**
     * A count that no container of the size can come to is found out at once, however many kinds
     * there are: nothing is handed to a kind.
     */
    @Test
    void aCountNoSizeCanComeToIsFoundOutAtTheFirstKind() {
        int kinds = 40;
        boolean[][] meets = new boolean[kinds][1];
        for (int kind = 0; kind < kinds; kind++) {
            meets[kind][0] = kind % 2 == 0;
        }
        boolean[][] asked = new boolean[1][17];
        asked[0][16] = false;
        asked[0][5] = false;
        SharingsAmongKinds sharings = new SharingsAmongKinds(meets, asked, -1, 4096);
        int[] each = {0};
        for (int size = 0; size <= 16; size++) {
            assertTrue(sharings.ofSize(size, shared -> {
                each[0]++;
                return true;
            }));
        }
        assertEquals(0, each[0]);
        assertEquals(0, sharings.looked());
        assertFalse(sharings.spent());
    }

    /**
     * Where every sharing gives a count asked for, there is nothing to drop and the figure is
     * what holds the walk: it stops exactly there, with far fewer of the sharings than there are.
     */
    @Test
    void theWalkIsHeldToTheFigureWhereNothingIsDropped() {
        int kinds = 16;
        boolean[][] meets = new boolean[kinds][1];
        boolean[][] asked = new boolean[1][17];
        for (int count = 0; count <= 16; count++) {
            asked[0][count] = true;
        }
        SharingsAmongKinds sharings = new SharingsAmongKinds(meets, asked, -1, 1000);
        int[] each = {0};
        boolean carriedOn = true;
        for (int size = 0; size <= 16 && carriedOn; size++) {
            carriedOn = sharings.ofSize(size, shared -> {
                each[0]++;
                return true;
            });
        }
        assertFalse(carriedOn);
        assertTrue(sharings.spent());
        assertEquals(1001, sharings.looked());
        assertTrue(each[0] <= 1000, () -> "sharings given: " + each[0]);
    }

    /** And where the one given each sharing says to stop, the walk stops. */
    @Test
    void theWalkStopsWhereTheOneItIsGivenSaysSo() {
        boolean[][] meets = {{true}, {false}};
        boolean[][] asked = new boolean[1][5];
        Arrays.fill(asked[0], true);
        SharingsAmongKinds sharings = new SharingsAmongKinds(meets, asked, -1, 1 << 20);
        int[] each = {0};
        assertFalse(sharings.ofSize(4, shared -> {
            each[0]++;
            return false;
        }));
        assertEquals(1, each[0]);
        assertFalse(sharings.spent());
    }
}
