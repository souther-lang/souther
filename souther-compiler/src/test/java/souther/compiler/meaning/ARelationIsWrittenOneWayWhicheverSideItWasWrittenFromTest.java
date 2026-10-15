package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A relation written either way round is one relation, and the way it is written holds exactly where
 * what was stated does.
 *
 * <p>Held over every form of two atoms with small coefficients, every relation and every point of a
 * small grid, so the turning of a form and of its relation is checked against the numbers rather
 * than against a table of what each relation turns into.
 */
class ARelationIsWrittenOneWayWhicheverSideItWasWrittenFromTest {

    private static final Quantity X = atom("x");
    private static final Quantity Y = atom("y");
    private static final List<Long> SMALL = List.of(-2L, -1L, 0L, 1L, 2L);

    @Test
    void whatIsWrittenHoldsExactlyWhereWhatWasStatedDoes() {
        for (long c : SMALL) {
            for (long a : SMALL) {
                for (long b : SMALL) {
                    LinearForm<Quantity> form = form(c, a, b);
                    for (Rel states : Rel.values()) {
                        Relation.OneWay<Quantity> one = Relation.OneWay.of(form, states);
                        assertEquals(one.proposition(), one.proposition().orItsDenial(),
                                "the canonical one of a relation and its denial");
                        assertFalse(Relation.OneWay.facesTheOtherWay(one.form()),
                                () -> one.form() + " faces the one way");
                        for (long x : SMALL) {
                            for (long y : SMALL) {
                                boolean stated = states.holds(valueAt(form, x, y));
                                boolean written = one.holds()
                                        == one.proposition().holds(valueAt(one.form(), x, y));
                                assertEquals(stated, written, () -> form + " " + states
                                        + " written as " + one + " at x=" + x + ", y=" + y);
                            }
                        }
                    }
                }
            }
        }
    }

    /**
     * Over a form with an atom in it. One with none is a number, and a relation of a number is
     * settled where it is met rather than written: nought standing at or above nought and at or
     * below it are both true, and no way of facing tells them apart.
     */
    @Test
    void aRelationAndItsMirrorAreWrittenAlike() {
        for (long c : SMALL) {
            for (long a : SMALL) {
                for (long b : SMALL) {
                    if (a == 0 && b == 0) {
                        continue;
                    }
                    LinearForm<Quantity> form = form(c, a, b);
                    for (Rel states : Rel.values()) {
                        assertEquals(Relation.OneWay.of(form, states),
                                Relation.OneWay.of(form.negate(), mirrored(states)),
                                () -> form + " " + states + " and its mirror");
                    }
                }
            }
        }
    }

    @Test
    void aRelationWrittenTheOtherWayIsRefused() {
        assertThrows(IllegalArgumentException.class,
                () -> new Relation.Affine(form(0, -1, 1), Rel.GE));
        assertTrue(new Relation.Affine(form(0, 1, -1), Rel.GE).form().coefs().containsKey(X));
    }

    private static Rel mirrored(Rel rel) {
        return switch (rel) {
            case GE -> Rel.LE;
            case GT -> Rel.LT;
            case LE -> Rel.GE;
            case LT -> Rel.GT;
            case EQ -> Rel.EQ;
            case NE -> Rel.NE;
        };
    }

    private static Quantity atom(String name) {
        return new DecisionAtom.OfTheInput(new NumericTerm.ValueOf(TermPath.of(name)));
    }

    private static LinearForm<Quantity> form(long constant, long ofX, long ofY) {
        Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>();
        if (ofX != 0) {
            coefs.put(X, ExactRatio.of(ofX));
        }
        if (ofY != 0) {
            coefs.put(Y, ExactRatio.of(ofY));
        }
        return new LinearForm<>(ExactRatio.of(constant), coefs);
    }

    /** The sign of {@code form} where its atoms are {@code x} and {@code y}. */
    private static int valueAt(LinearForm<Quantity> form, long x, long y) {
        ExactRatio at = form.constant();
        for (Map.Entry<Quantity, ExactRatio> each : form.coefs().entrySet()) {
            ExactRatio value = ExactRatio.of(each.getKey().equals(X) ? x : y);
            at = at.plus(each.getValue().times(value).orNull()).orNull();
        }
        return at.signum();
    }
}
