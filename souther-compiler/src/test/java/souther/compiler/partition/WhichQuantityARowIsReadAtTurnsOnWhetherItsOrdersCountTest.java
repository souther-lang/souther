package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.ExactAnswer;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Text;
import souther.compiler.numeric.UnheldNumber;

import java.util.LinkedHashMap;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNull;

/**
 * The quantity a row is read at to say whether a relation over the input's numbers holds there is
 * a sum where every order has numbers under it, the two positions apart where two strings are held
 * against each other, and none where neither is so.
 *
 * <p>None is an answer and not a refusal: a reader of rows says it could not read such a relation,
 * which is what a sum of what has no number comes to.
 */
class WhichQuantityARowIsReadAtTurnsOnWhetherItsOrdersCountTest {

    private static final NumericTerm X = new NumericTerm.ValueOf(TermPath.of("x"));

    private static final NumericTerm U = new NumericTerm.ValueOf(TermPath.of("u"));

    private static final NumericTerm W = new NumericTerm.ValueOf(TermPath.of("w"));

    private static Map<NumericTerm, TermOrders> on(Carrier carrier, NumericTerm... terms) {
        Map<NumericTerm, TermOrders> out = new LinkedHashMap<>();
        for (NumericTerm term : terms) {
            out.put(term, TermOrdersFixtures.itself(term, carrier));
        }
        return out;
    }

    private static LinearForm<NumericTerm> weighing(Map<NumericTerm, ExactRatio> coefs) {
        return new LinearForm<>(ExactRatio.ZERO, coefs);
    }

    @Test
    void numbersAreReadAsTheirSum() {
        LinearQuantity read = Cutting.readAt("g", LinearForm.difference(X, U),
                on(Carrier.WHOLE, X, U));
        assertInstanceOf(BorderQuantity.OverAForm.class, read);
    }

    @Test
    void twoStringsHeldAgainstEachOtherAreReadApart() {
        LinearQuantity read = Cutting.readAt("g", LinearForm.difference(X, U),
                on(Carrier.TEXT, X, U));
        assertInstanceOf(BorderQuantity.Apart.class, read);
    }

    /** Three strings, or two weighed other than one against the other, are no pair and no sum. */
    @Test
    void aFormOfStringsThatIsNoPairIsReadAtNoQuantity() {
        Map<NumericTerm, ExactRatio> three = new LinkedHashMap<>();
        three.put(X, ExactRatio.ONE);
        three.put(U, ExactRatio.ONE.negated());
        three.put(W, ExactRatio.ONE);
        assertNull(Cutting.readAt("g", weighing(three), on(Carrier.TEXT, X, U, W)));

        Map<NumericTerm, ExactRatio> twice = new LinkedHashMap<>();
        twice.put(X, ExactRatio.of(2));
        twice.put(U, ExactRatio.ONE.negated());
        assertNull(Cutting.readAt("g", weighing(twice), on(Carrier.TEXT, X, U)));
    }

    /** A sum taken at a position with no numbers under it is no sum, and moving one there says so
     *  rather than making the sum it cannot be. */
    @Test
    void aSumMovedOntoAnOrderWithNoNumbersIsNone() {
        LinearQuantity sum = Cutting.readAt("g", LinearForm.difference(X, U),
                on(Carrier.WHOLE, X, U));
        assertNull(sum.movedTo(X, TermOrdersFixtures.itself(W, Carrier.TEXT)));
        assertInstanceOf(BorderQuantity.OverAForm.class,
                sum.movedTo(X, TermOrdersFixtures.itself(W, Carrier.WHOLE)));
    }

    /**
     * Which side a row stands on is the order of the string weighed by one against the one weighed
     * by minus one, whichever way round the form holds them: {@code x - u} is below nought where
     * {@code x} is below {@code u}, and {@code u - x} is above it there.
     */
    @Test
    void whichSideOfNoughtTwoStringsComeToIsTheOrderOfTheFirstAgainstTheOther() {
        LinearQuantity xLessU = Cutting.readAt("g", LinearForm.difference(X, U),
                on(Carrier.TEXT, X, U));
        LinearQuantity uLessX = Cutting.readAt("g", LinearForm.difference(U, X),
                on(Carrier.TEXT, X, U));
        Map<NumericTerm, Place> below = Map.of(X, Text.of("a"), U, Text.of("b"));
        Map<NumericTerm, Place> level = Map.of(X, Text.of("a"), U, Text.of("a"));

        assertEquals(ExactAnswer.held(-1), xLessU.signAt(below, ExactRatio.ZERO));
        assertEquals(ExactAnswer.held(1), uLessX.signAt(below, ExactRatio.ZERO));
        assertEquals(ExactAnswer.held(0), xLessU.signAt(level, ExactRatio.ZERO));
    }

    /** Two strings stand no number apart, so a relation holding them some distance apart is one no
     *  row of them can be read at, and the place one comes level with the other is none. */
    @Test
    void twoStringsSomeDistanceApartAreNothingARowCanBeReadAt() {
        LinearQuantity read = Cutting.readAt("g", LinearForm.difference(X, U),
                on(Carrier.TEXT, X, U));
        Map<NumericTerm, Place> values = Map.of(X, Text.of("a"), U, Text.of("b"));

        assertEquals(ExactAnswer.unheld(UnheldNumber.NO_REPRESENTATION_EXISTS),
                read.signAt(values, ExactRatio.ONE));
        assertNull(read.levelWith(X, ExactRatio.ONE, values));
        assertEquals(Text.of("b"), read.levelWith(X, ExactRatio.ZERO, values));
        assertEquals(Text.of("a"), read.levelWith(U, ExactRatio.ZERO, values));
    }
}
