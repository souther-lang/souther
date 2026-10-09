package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.TermOrders;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.numeric.ExactRatio;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What a count of the elements of a container is of: the container, what an element is counted for
 * meeting, and that statement as rows are asked it.
 *
 * <p>Apart from the quantity a line on the count is drawn on. A row composed for a count, a
 * condition on the way that holds one against a number and a line on it all ask what is counted,
 * and only the last is a quantity a border stands on; held as the quantity, every one of them would
 * be a reader asking which quantity a border is on.
 *
 * @param behavior   the behavior whose input the container is in
 * @param container  the container the elements are counted in
 * @param meeting    what an element is counted for meeting, over the element's own numbers and the
 *                   input's
 * @param perElement {@code meeting} put to rows, which is what an element is asked
 * @param on         the order each number {@code perElement} reads is written on, where the input's
 *                   reading has one
 */
record CountedElements(String behavior, TermPath container, Proposition meeting,
                       AStatementAtARow perElement, Map<NumericTerm, Carrier> on) {

    CountedElements {
        if (behavior == null || container == null || meeting == null || perElement == null) {
            throw new IllegalArgumentException("a count is a behavior's count of the elements of"
                    + " some container meeting something");
        }
        on = Map.copyOf(on);
    }

    /**
     * How many elements of {@code count}'s container meet its statement, as {@code behavior} reads
     * it, for a statement {@link AStatementAtARow#askable} says a row can be asked.
     *
     * <p>The one way one of these is made, wherever the count is met: a line drawn on it and a
     * condition on the way to another are the same count where they count the same thing.
     */
    static CountedElements of(String behavior, Quantity.HowManyMeet count, Quantities quantities) {
        AStatementAtARow perElement =
                AStatementAtARow.of(count.ofTheElement(), behavior, quantities);
        Map<NumericTerm, Carrier> on = new LinkedHashMap<>();
        for (NumericTerm each : perElement.numbers()) {
            TermOrders orders = quantities.ordersOf(each);
            if (orders != null && orders.observed() != null) {
                on.put(each, orders.observed());
            }
        }
        return new CountedElements(behavior, count.container(), count.ofTheElement(), perElement,
                on);
    }

    /** Every number of a row the statement reads, the element's own among them. */
    List<NumericTerm> numbers() {
        return perElement.numbers();
    }

    /** The counts there are: every whole number, from none. */
    LevelSpace levels() {
        return LevelSpace.steppingBy(ExactRatio.ONE);
    }

    @Override
    public String toString() {
        return "#" + container + " [" + meeting.key() + "]";
    }
}
