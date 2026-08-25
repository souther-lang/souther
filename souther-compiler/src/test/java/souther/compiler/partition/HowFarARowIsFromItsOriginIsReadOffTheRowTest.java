package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * How far a row is from the value it is written against, and which fields that means writing over.
 *
 * <p>One difference and two readers. The search walks the assignments nearest this first; the row is
 * written as the origin with the fields this names moved over it. Counted twice — once as how many
 * positions the walk reached for, once as which fields to write — the two were free to disagree, and
 * did: the position a row was about was written over whatever it held, because the walk counted it
 * as moved for being the target rather than for the row differing there.
 */
class HowFarARowIsFromItsOriginIsReadOffTheRowTest {

    /** A row standing where its origin does at every position is no distance from it. */
    @Test
    void aRowStandingWhereItsOriginDoesIsNoDistanceFromIt() {
        assertEquals(List.of(),
                Delta.between(new int[] {0, 1, 2}, new int[] {0, 1, 2}).at());
    }

    /** Only the positions that differ, in the axes' own order. */
    @Test
    void onlyThePositionsThatDifferAreInIt() {
        assertEquals(List.of(0, 2), Delta.between(new int[] {0, 1, 2}, new int[] {1, 1, 0}).at());
        assertEquals(2, Delta.between(new int[] {0, 1, 2}, new int[] {1, 1, 0}).size());
    }

    /**
     * A position the row stands at no class of differs from an origin that stands at one.
     *
     * <p>Which is a real difference and is written down as one. A row under one case of a sum is at
     * no class of the positions under another, and an origin that stands at one of those is a value
     * this row does not resemble there.
     */
    @Test
    void standingNowhereDiffersFromStandingSomewhere() {
        assertEquals(List.of(1), Delta.between(new int[] {0, 1}, new int[] {0, -1}).at());
        assertEquals(List.of(1), Delta.between(new int[] {0, -1}, new int[] {0, 1}).at());
    }

    /** And standing nowhere in both is no difference: neither is a class the row holds. */
    @Test
    void standingNowhereInBothIsNoDifference() {
        assertEquals(List.of(), Delta.between(new int[] {-1, -1}, new int[] {-1, -1}).at());
    }
}
