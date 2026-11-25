package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.Rel;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * The levels that stand to a level as a relation says, held to {@link Rel#holds} below the level,
 * at it and above it.
 */
class TheRegionARelationDescribesHoldsWhereTheRelationDoesTest {

    @Test
    void aLevelIsInTheRegionWhereTheRelationHoldsOfIt() {
        ExactRatio at = ExactRatio.of(5);
        for (Rel rel : Rel.values()) {
            LevelRegion region = LevelRegion.where(rel, new Level.OfTheQuantity(at));
            for (int sign = -1; sign <= 1; sign++) {
                ExactRatio value = at.plus(ExactRatio.of(sign)).orNull();
                int stands = sign;
                assertEquals(rel.holds(stands), region.contains(new Level.OfTheQuantity(value)),
                        () -> "a level standing " + stands + " from the one " + rel
                                + " is written against");
            }
        }
    }
}
