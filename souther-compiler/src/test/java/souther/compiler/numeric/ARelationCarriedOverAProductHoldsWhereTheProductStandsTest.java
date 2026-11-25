package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A relation of a form to nought, said again of the form multiplied by a factor of a given sign,
 * and a relation said where a statement of it holds or is denied.
 *
 * <p>Held to {@link Rel#holds} at each way the form can stand to nought: what the relation said of
 * the form is what the carried relation says of the product. A factor above nought and one below
 * it, and nought, which carries nothing.
 */
class ARelationCarriedOverAProductHoldsWhereTheProductStandsTest {

    @Test
    void whatHeldOfTheFormHoldsOfTheProduct() {
        for (Rel rel : Rel.values()) {
            for (int factor : new int[] {-1, 1}) {
                for (int sign = -1; sign <= 1; sign++) {
                    int stands = sign;
                    int by = factor;
                    assertEquals(rel.holds(stands), rel.scaledBySign(by).holds(stands * by),
                            () -> rel + " of a form standing " + stands + " from nought, times a"
                                    + " factor of sign " + by);
                }
            }
        }
    }

    @Test
    void noughtCarriesNoRelation() {
        for (Rel rel : Rel.values()) {
            assertThrows(IllegalArgumentException.class, () -> rel.scaledBySign(0));
        }
    }

    @Test
    void aStatementDeniedStatesTheDenial() {
        for (Rel rel : Rel.values()) {
            assertEquals(rel, rel.whenHolding(true));
            for (int sign = -1; sign <= 1; sign++) {
                assertEquals(!rel.holds(sign), rel.whenHolding(false).holds(sign),
                        () -> rel + " denied");
            }
        }
    }
}
