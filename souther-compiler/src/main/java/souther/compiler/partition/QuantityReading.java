package souther.compiler.partition;

import souther.compiler.inputs.TermOrders;

import java.util.List;
import java.util.Map;

/**
 * What was read at one row, for each of the orders a quantity reads its terms on.
 *
 * <p>The row read, and not an answer about it. {@link BorderQuantity#standsAt} ranks what the terms
 * came to one way and {@link BorderQuantity#valuesOf} ranks it another — a position the row wrote
 * nothing at outranks what stopped a reading for the first and is put together with it for the
 * second — so neither of their answers can be had from the other, and a walk of the row that came
 * back as either would be a walk the other question has to make again.
 *
 * <p><b>Asked for by {@link TermOrders} and not by the term.</b> What a term read depends on both
 * which term it is and what its value was decoded on: the same position read on one order and on
 * another are two numbers, and one of them is no number at all. Held under the term alone, a reading
 * made on one order answers for a quantity that reads that position on another — which is a verdict
 * about a row taken from a value it does not hold. The orders carry which term they are of
 * ({@link TermOrders#term}), so asking with them asks both questions at once.
 *
 * <p><b>And there is no way to read the entries.</b> A consumer asks for the readings its own
 * quantity needs; it does not interpret whatever entries happen to be here. Handed the pair set, a
 * reader would fold what it was given — which is how a fold came to answer for one quantity with
 * another's values — and every fold added would have to re-derive for itself which entries are its
 * to read.
 *
 * <p>Two quantities that read the same terms on the same orders make the same reading, and either
 * may be answered from it. That is not a way round the above: the row was read the same way, and
 * what differs between them is what they weigh those numbers by.
 */
final class QuantityReading {

    private final Map<TermOrders, WhatATermRead> answers;

    QuantityReading(Map<TermOrders, WhatATermRead> answers) {
        if (answers == null || answers.isEmpty()) {
            throw new IllegalArgumentException("a quantity is taken of at least one term, so a"
                    + " reading of one answers for at least one");
        }
        // No order kept, because nothing reads these in any order. What a reader wants is the entry
        // for the orders it holds, and the one place an order is wanted is a message.
        this.answers = Map.copyOf(answers);
    }

    /**
     * What was read at {@code orders}, which this reading has to have been read on.
     *
     * <p>Refused rather than answered for. A reading this was not made on is not a term this went
     * without: it is a reading of the row under orders this quantity does not read it on, and an
     * answer to it would be a number the row does not hold at a position it does.
     */
    WhatATermRead of(TermOrders orders) {
        WhatATermRead answer = answers.get(orders);
        if (answer == null) {
            throw new IllegalArgumentException("this row was read at " + answersFor()
                    + " and was asked what it read at " + orders);
        }
        return answer;
    }

    /**
     * What this was read at, in one order.
     *
     * <p>Spelled and sorted rather than taken in the order the entries are held: nothing here keeps
     * an order, a message that changes between runs cannot be compared between runs, and this is
     * the only place any of them is looked at outside the entry a caller asked for.
     */
    private List<String> answersFor() {
        return answers.keySet().stream().map(TermOrders::toString).sorted().toList();
    }

    @Override
    public String toString() {
        return "QuantityReading" + answersFor();
    }
}
