package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.DeclarationAccess;
import souther.compiler.check.Extreme;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermOrdersFixtures;
import souther.compiler.inputs.TermPath;
import souther.compiler.numeric.Count;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbols;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * A number of an element read off the elements beside it is read on a row among the elements of
 * the occurrence of its container the reading is in, and not among every value standing at the
 * place: the lines of two orders are two sets of lines.
 *
 * <p>The row here is two orders, the first holding one line of {@code x} at nine and the second one
 * line of {@code x} at two, read with the first order's line chosen. Read off every value at the
 * place, {@code x} would occur twice and its least would be two.
 */
class ANumberOfAnElementIsReadAmongItsOwnOccurrenceTest {

    private static final TermPath ORDERS = TermPath.of("orders");

    private static final TermPath LINES = ORDERS.element().then("lines");

    private static final Carrier WHOLE = Carrier.ofValue(Type.Prim.INT, DeclarationAccess.NONE);

    @Test
    void howOftenAValueOccursIsCountedInItsOwnOrder() {
        TermOrders on = TermOrdersFixtures.itself(
                NumericTerm.Multiplicity.of(LINES, LINES.element().then("sku")), Carrier.TEXT);
        assertEquals(new WhatATermRead.Number(Count.of(1)),
                WhatATermRead.inItsOccurrence(on, new TwoOrders(0, 0)));
    }

    @Test
    void theEndOfAKeysValuesIsTakenInItsOwnOrder() {
        NumericTerm.ExtremeOfItsKey least = NumericTerm.ExtremeOfItsKey.of(LINES,
                LINES.element().then("sku"), LINES.element().then("qty"), Extreme.LEAST);
        TermOrders on = TermOrdersFixtures.computed(least, WHOLE, WHOLE,
                Map.of(least.keyField(), Carrier.TEXT));
        assertEquals(new WhatATermRead.Number(Count.of(9)),
                WhatATermRead.inItsOccurrence(on, new TwoOrders(0, 0)));
    }

    /** A reading that chose no line is about none of them, which is no number here. */
    @Test
    void aReadingThatChoseNoElementHasNoNumber() {
        TermOrders on = TermOrdersFixtures.itself(
                NumericTerm.Multiplicity.of(LINES, LINES.element().then("sku")), Carrier.TEXT);
        assertInstanceOf(WhatATermRead.NothingWrittenThere.class,
                WhatATermRead.inItsOccurrence(on, new TwoOrders(0, null)));
    }

    private static ObservedValue line(String sku, long qty) {
        return new ObservedValue.Constructed(TypeSymbols.declared(new TypeKey("demo", "Line")),
                Map.of("sku", new ObservedValue.Text(sku), "qty", new ObservedValue.Integer(qty)));
    }

    /**
     * Two orders, each holding one line of {@code x}, read with order {@code order} chosen and
     * {@code chosenLine} of its lines; every value at a place is both orders'.
     */
    private record TwoOrders(int order, Integer chosenLine)
            implements BorderQuantity.Observation {

        private static final List<List<ObservedValue>> LINES_OF = List.of(
                List.of(line("x", 9)), List.of(line("x", 2)));

        @Override
        public WalkResult<ObservationAtPoint> at(TermPath path) {
            if (chosenLine == null) {
                return WalkResult.reached(new ObservationAtPoint.WroteNothing());
            }
            ObservedValue chosen = LINES_OF.get(order).get(chosenLine);
            String field = path.steps().getLast().toString();
            return WalkResult.reached(new ObservationAtPoint.Value(
                    ((ObservedValue.Constructed) chosen).field(field)));
        }

        @Override
        public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
            String field = path.steps().getLast().toString();
            List<ObservedValue> every = new ArrayList<>();
            LINES_OF.forEach(lines -> lines.forEach(one ->
                    every.add(((ObservedValue.Constructed) one).field(field))));
            return WalkResult.reached(every);
        }

        /** The lines of the order this reading chose, as the walk over a row answers them. */
        @Override
        public WalkResult<List<BorderQuantity.Observation>> eachElementOf(TermPath container) {
            List<BorderQuantity.Observation> out = new ArrayList<>();
            for (int each = 0; each < LINES_OF.get(order).size(); each++) {
                out.add(new TwoOrders(order, each));
            }
            return WalkResult.reached(out);
        }
    }
}
