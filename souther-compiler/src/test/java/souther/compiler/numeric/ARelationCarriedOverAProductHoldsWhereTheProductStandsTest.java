package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A relation of a form to nought, said again of the form multiplied by a number, and a relation
 * said where a statement of it holds or is denied.
 *
 * <p>Held to {@link Rel#holds} at each way the form can stand to nought: what the relation said of
 * the form is what the carried relation says of the product. A factor above nought and one below
 * it, a whole one and a part of one, and nought, which carries nothing.
 */
class ARelationCarriedOverAProductHoldsWhereTheProductStandsTest {

    private static final ExactRatio[] FACTORS = {
            ExactRatio.of(3), ExactRatio.of(-2),
            ExactRatio.of(1).dividedBy(ExactRatio.of(2)).orNull(),
            ExactRatio.of(-1).dividedBy(ExactRatio.of(3)).orNull()};

    @Test
    void whatHeldOfTheFormHoldsOfTheProduct() {
        for (Rel rel : Rel.values()) {
            for (ExactRatio factor : FACTORS) {
                for (int sign = -1; sign <= 1; sign++) {
                    int product = sign * factor.signum();
                    int stands = sign;
                    assertEquals(rel.holds(stands), rel.scaledBy(factor).holds(product),
                            () -> rel + " of a form standing " + stands + " from nought, times "
                                    + factor);
                }
            }
        }
    }

    @Test
    void noughtCarriesNoRelation() {
        for (Rel rel : Rel.values()) {
            assertThrows(IllegalArgumentException.class, () -> rel.scaledBy(ExactRatio.ZERO));
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
