package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.check.Carrier;
import souther.compiler.check.NewtypeInners;
import souther.compiler.check.Symbols;
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Function;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertNotNull;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A run of what was computed of each element by where it stands claims the order of the elements,
 * holds what showed it, and is read in that order.
 *
 * <p>A total of such numbers turns on which element stands where: weighed one and three by
 * position, {@code [2, 4]} comes to fourteen and {@code [4, 2]} to ten. So a run of one is made only
 * with what showed the walk was handed the elements in the order the row writes them, is not moved
 * to elements nothing showed that of, and is read with each element at the place it was handed in.
 * A run of a computation that turns on no position claims nothing of the order, and is the same run
 * however the walk that reached it ordered them.
 */
class ARunComputedByPositionClaimsTheOrderItWasShownTest {

    private static final TermPath ELEMENTS = TermPath.of("xs").element();
    private static final ElementProjection ITSELF = ElementProjection.ofFields(List.of());

    private static ElementValue.Affine weighed(long weight) {
        return new ElementValue.Affine(new LinearForm<>(ExactRatio.ZERO,
                Map.of(ITSELF, ExactRatio.of(weight))));
    }

    /** One where the position is even and three where it is odd. */
    private static final ElementValue BY_POSITION = new ElementValue.ByPosition(
            new ElementValue.PositionTest(2, Rel.EQ, 0), weighed(1), weighed(3));

    private static NumericTerm.TakenOver total(RunSource run) {
        return NumericTerm.TakenOver.of(ValueName.Stdlib.operation("List", "sum"), run,
                Type.Prim.INT, NewtypeInners.NONE, Symbols.none(DefaultStdlib.get()));
    }

    private static Count read(RunSource run, long... elements) {
        Map<ElementProjection, Carrier> fields = new LinkedHashMap<>();
        fields.put(ITSELF, new Carrier.Whole());
        TermOrders orders = TermOrdersFixtures.computed(total(run), new Carrier.Whole(),
                new Carrier.Whole(), fields);
        List<Function<ElementProjection, ObservedValue>> each = new ArrayList<>();
        for (long element : elements) {
            each.add(field -> new ObservedValue.Integer(element));
        }
        return (Count) assertInstanceOf(NumericTerm.Reading.Number.class,
                orders.readOverElements(each)).value();
    }

    /** Each element takes the weight of where it stands, so the same values in another order are
     *  another total, and two equal values are weighed by their places and not by their value. */
    @Test
    void eachElementIsWeighedByWhereItStands() {
        RunSource run = RunSource.computedOverTheElementsAt(ELEMENTS, BY_POSITION, Type.Prim.INT,
                new RunSource.InTheOrderWritten(ELEMENTS, false));
        assertNotNull(run);
        assertEquals(Count.of(2 + 3 * 4), read(run, 2, 4));
        assertEquals(Count.of(4 + 3 * 2), read(run, 4, 2));
        assertEquals(Count.of(5 + 3 * 5 + 5), read(run, 5, 5, 5));
        assertEquals(Count.of(7), read(run, 7), "the first element stands at nought");
        assertEquals(Count.of(0), read(run), "and none comes to what the walk starts from");
    }

    /** Handed the last element first, the first handed stands at nought: the same row is another
     *  total, and is not the run of the near end. */
    @Test
    void eachElementHandedFromTheFarEndIsWeighedByWhereItStandsThere() {
        RunSource run = RunSource.computedOverTheElementsAt(ELEMENTS, BY_POSITION, Type.Prim.INT,
                new RunSource.InTheOrderWritten(ELEMENTS, true));
        assertNotNull(run);
        assertEquals(Count.of(4 + 3 * 2), read(run, 2, 4));
        assertEquals(Count.of(2 + 3 * 4), read(run, 4, 2));
        assertEquals(Count.of(5 + 3 * 5 + 5), read(run, 5, 5, 5));
        assertNotEquals(run, RunSource.computedOverTheElementsAt(ELEMENTS, BY_POSITION,
                Type.Prim.INT, new RunSource.InTheOrderWritten(ELEMENTS, false)));
    }

    /** Without what showed the order, a run that turns on it is none; with it, only of the
     *  elements it was shown of. */
    @Test
    void aRunThatTurnsOnThePositionIsMadeOnlyWithTheOrderShown() {
        assertNull(RunSource.computedOverTheElementsAt(ELEMENTS, BY_POSITION, Type.Prim.INT,
                null));
        assertThrows(IllegalArgumentException.class, () -> new RunSource.ComputedOccurrences(
                ELEMENTS, BY_POSITION, Type.Prim.INT, null));
        RunSource.InTheOrderWritten elsewhere =
                new RunSource.InTheOrderWritten(TermPath.of("ys").element(), false);
        assertNull(RunSource.computedOverTheElementsAt(ELEMENTS, BY_POSITION, Type.Prim.INT,
                elsewhere));
        assertThrows(IllegalArgumentException.class, () -> new RunSource.ComputedOccurrences(
                ELEMENTS, BY_POSITION, Type.Prim.INT, elsewhere));
    }

    /** A run that turns on no position claims nothing of the order, whatever showed it. */
    @Test
    void aRunThatTurnsOnNoPositionClaimsNoOrder() {
        RunSource.InTheOrderWritten shown =
                new RunSource.InTheOrderWritten(ELEMENTS, false);
        assertEquals(RunSource.computedOverTheElementsAt(ELEMENTS, weighed(3), Type.Prim.INT,
                        null),
                RunSource.computedOverTheElementsAt(ELEMENTS, weighed(3), Type.Prim.INT, shown),
                "one run, however the walk reaching it ordered the elements");
        assertThrows(IllegalArgumentException.class, () -> new RunSource.ComputedOccurrences(
                ELEMENTS, weighed(3), Type.Prim.INT, shown));
    }

    /** What was shown of the order was shown where the elements stood, so a run that needs it does
     *  not move, and one that does not, does. */
    @Test
    void aRunThatTurnsOnThePositionDoesNotMove() {
        RunSource byPosition = RunSource.computedOverTheElementsAt(ELEMENTS, BY_POSITION,
                Type.Prim.INT, new RunSource.InTheOrderWritten(ELEMENTS, false));
        TermPath moved = TermPath.of("ys").element();
        assertNull(byPosition.movedTo(_ -> moved));
        RunSource alike = RunSource.computedOverTheElementsAt(ELEMENTS, weighed(3), Type.Prim.INT,
                null);
        assertEquals(moved, alike.movedTo(_ -> moved).subjectPath());
    }

    /**
     * Whether a computation turns on the position is asked of all of it, and a choice by position
     * whose answers are one answer turns on nothing.
     */
    @Test
    void whetherItTurnsOnThePositionIsAskedOfAllOfIt() {
        assertTrue(BY_POSITION.readsThePosition());
        assertFalse(weighed(3).readsThePosition());
        ElementValue flagged = ElementValue.choosing(ElementProjection.ofFields(List.of("debit")),
                BY_POSITION, weighed(1));
        assertTrue(flagged.readsThePosition(), "inside a choice by a flag");
        Map<ElementValue, ExactRatio> chosen = new LinkedHashMap<>();
        chosen.put(BY_POSITION, ExactRatio.ONE);
        chosen.put(flagged, ExactRatio.ONE);
        assertTrue(ElementValue.summed(ExactRatio.ZERO, Map.of(), chosen).readsThePosition(),
                "and among choices added up");
        ElementValue alike = ElementValue.choosingByPosition(
                new ElementValue.PositionTest(2, Rel.EQ, 0), weighed(3), weighed(3));
        assertEquals(weighed(3), alike);
        assertFalse(alike.readsThePosition());
    }

    /** A choice of numbers times a form weighs the form by whichever number the element chose. */
    @Test
    void aChoiceOfNumbersTimesAFormWeighsTheForm() {
        ElementValue weight = new ElementValue.ByPosition(
                new ElementValue.PositionTest(2, Rel.EQ, 0),
                new ElementValue.Affine(LinearForm.constant(ExactRatio.ONE)),
                new ElementValue.Affine(LinearForm.constant(ExactRatio.of(3))));
        assertEquals(BY_POSITION, ElementValue.weighedBy(weight, weighed(1)));
        assertNull(ElementValue.weighedBy(BY_POSITION, weighed(1)),
                "a choice whose answers read the element is no weight");
    }
}
