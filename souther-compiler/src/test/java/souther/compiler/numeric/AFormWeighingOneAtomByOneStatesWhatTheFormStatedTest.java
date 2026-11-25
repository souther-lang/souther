package souther.compiler.numeric;

import org.junit.jupiter.api.Test;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A comparison of a form with nought said again of the form weighing one of its atoms by one, and
 * the one atom a form weighs.
 *
 * <p>Held to the comparison itself at every point of a small grid: where {@code form rel 0} held,
 * the statement it became holds, and nowhere else. A weight below nought turns the relation round,
 * which is the half a reader writing it out drops. And a weight at the least exponent, whose
 * reciprocal no ratio holds: the form divided by it is still a form, so the statement is still
 * there to make.
 */
class AFormWeighingOneAtomByOneStatesWhatTheFormStatedTest {

    private static final List<LinearForm<String>> FORMS = List.of(
            form(-6, Map.of("a", 2L)),
            form(9, Map.of("a", -3L, "b", 1L)),
            form(1, Map.of("a", -1L, "b", -2L)));

    @Test
    void theStatementHoldsWhereTheComparisonDid() {
        for (LinearForm<String> form : FORMS) {
            for (Rel rel : Rel.values()) {
                LinearForm.Stated<String> one = form.weighingOne("a", rel).orNull();
                assertEquals(ExactRatio.ONE, one.form().coefs().get("a"));
                for (long a = -4; a <= 4; a++) {
                    for (long b = -4; b <= 4; b++) {
                        Map<String, Long> at = Map.of("a", a, "b", b);
                        assertEquals(rel.holds(valueOf(form, at).signum()),
                                one.rel().holds(valueOf(one.form(), at).signum()),
                                () -> form + " " + rel + " 0 at " + at);
                    }
                }
            }
        }
    }

    @Test
    void aWeightWhoseReciprocalNoRatioHoldsStillDivides() {
        ExactRatio least = ExactRatio.tenTo(Long.MIN_VALUE);
        assertInstanceOf(ExactAnswer.Unheld.class, ExactRatio.ONE.dividedBy(least),
                "the weight is one whose reciprocal no ratio holds");
        LinearForm<String> form = new LinearForm<>(least, Map.of("a", least));
        LinearForm.Stated<String> one = form.weighingOne("a", Rel.GE).orNull();
        assertEquals(new LinearForm<>(ExactRatio.ONE, Map.of("a", ExactRatio.ONE)), one.form());
        assertEquals(Rel.GE, one.rel());
    }

    @Test
    void anAtomTheFormDoesNotWeighIsRefused() {
        assertThrows(IllegalArgumentException.class,
                () -> FORMS.getFirst().weighingOne("b", Rel.GE));
        assertThrows(IllegalArgumentException.class,
                () -> new LinearForm<>(ExactRatio.ONE, Map.of("a", ExactRatio.ZERO))
                        .weighingOne("a", Rel.GE));
    }

    @Test
    void theLoneAtomIsTheOneOfOneAndNoneOfTwo() {
        LinearForm<String> one = form(3, Map.of("x", 2L));
        assertEquals("x", one.loneAtom());
        assertEquals(Map.entry("x", ExactRatio.of(2)), one.loneTerm());
        assertNull(LinearForm.<String>constant(ExactRatio.of(3)).loneAtom());
        assertNull(LinearForm.<String>constant(ExactRatio.of(3)).loneTerm());
        assertNull(FORMS.get(1).loneAtom());
        assertNull(FORMS.get(1).loneTerm());
    }

    private static LinearForm<String> form(long constant, Map<String, Long> weights) {
        Map<String, ExactRatio> coefs = new LinkedHashMap<>();
        weights.forEach((atom, weight) -> coefs.put(atom, ExactRatio.of(weight)));
        return new LinearForm<>(ExactRatio.of(constant), coefs);
    }

    private static ExactRatio valueOf(LinearForm<String> form, Map<String, Long> at) {
        ExactRatio sum = form.constant();
        for (Map.Entry<String, ExactRatio> each : form.coefs().entrySet()) {
            sum = sum.plus(each.getValue().times(ExactRatio.of(at.get(each.getKey()))).orNull())
                    .orNull();
        }
        return sum;
    }
}
