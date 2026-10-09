package souther.compiler.meaning;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;

import java.math.BigDecimal;
import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A statement moved to a call stops, where it does, for what stopped it — and its weights are one
 * sum whatever order they come in.
 *
 * <p>Parameters handed one position are one number there, and their weights add. Where what they
 * add to is no number the exact arithmetic holds, that is what stopped the statement: a number not
 * held, and not a parameter handed a value at no position. And a count whose element statement
 * stopped at the call stopped for what that statement says stopped it.
 */
class AStatementMovedToACallStopsForWhatStoppedItTest {

    private static final ExactRatio FINE = ExactRatio.of(new BigDecimal(BigInteger.ONE, 1 << 30));

    private static final Map<String, TermPath> ALL_HANDED_ONE_POSITION = Map.of(
            "p", TermPath.of("x"), "q", TermPath.of("x"), "r", TermPath.of("x"));

    @Test
    void weightsAddingToANumberNotHeldStopForThatNumber() {
        Proposition moved = MovedToACall.of(compared(Map.of("p", ExactRatio.ONE, "q", FINE)),
                ALL_HANDED_ONE_POSITION, AStatementMovedToACallStopsForWhatStoppedItTest::unread);
        Proposition.Unread unread = assertInstanceOf(Proposition.Unread.class, moved);
        assertInstanceOf(WhyUnread.ANumberNotHeld.class, unread.why(),
                () -> "a number not held, and not a parameter at no position: " + unread.why());
    }

    @Test
    void weightsThatCancelAreMovedWhateverOrderTheyCome() {
        for (List<String> order : List.of(List.of("p", "q", "r"), List.of("q", "p", "r"),
                List.of("p", "r", "q"))) {
            Map<String, ExactRatio> weights = new LinkedHashMap<>();
            Map<String, ExactRatio> of = Map.of("p", FINE, "q", ExactRatio.ONE,
                    "r", FINE.negated());
            order.forEach(each -> weights.put(each, of.get(each)));
            Proposition moved = MovedToACall.of(compared(weights), ALL_HANDED_ONE_POSITION,
                    AStatementMovedToACallStopsForWhatStoppedItTest::unread);
            assertEquals(Proposition.stopsIn(moved), List.of(),
                    () -> "moved whole in the order " + order + ": " + moved);
        }
    }

    /** A count of the elements meeting something about a value the body binds, which a call
     *  cannot say: the count stops for that, and not for a parameter at no position. */
    @Test
    void aCountWhoseElementStoppedStopsForWhatStoppedTheElement() {
        Quantity bound = new Quantity.OfABinding(
                new BindingId(new BindingOwner.OfValue("m", "f"), 0), List.of(), Type.INT,
                Optional.empty());
        Proposition count = new Proposition.Compared(new Relation.Affine(
                LinearForm.<Quantity>atomMinusConstant(new Quantity.HowManyMeet(TermPath.of("p"),
                        new Proposition.Compared(new Relation.Affine(
                                LinearForm.atom(bound), Rel.GT), true)), ExactRatio.ONE),
                Rel.GT), true);
        Proposition moved = MovedToACall.of(count, ALL_HANDED_ONE_POSITION,
                AStatementMovedToACallStopsForWhatStoppedItTest::unread);
        assertEquals(List.of(new WhyUnread.InACalledBody(
                        WhyUnread.InACalledBody.What.A_VALUE_IT_BINDS)),
                Proposition.stopsIn(moved));
    }

    /** {@code weights} of the parameters, above nought. */
    private static Proposition compared(Map<String, ExactRatio> weights) {
        Map<Quantity, ExactRatio> coefs = new LinkedHashMap<>();
        weights.forEach((parameter, weight) -> coefs.put(new DecisionAtom.OfTheInput(
                new NumericTerm.ValueOf(TermPath.of(parameter))), weight));
        return new Proposition.Compared(new Relation.Affine(
                new LinearForm<>(ExactRatio.ZERO, coefs), Rel.GT), true);
    }

    private static Proposition unread(WhyUnread why) {
        return new Proposition.Unread(Optional.empty(), 0, why, false, true);
    }
}
