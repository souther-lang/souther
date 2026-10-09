package souther.compiler.partition;

import souther.compiler.check.Carrier;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermOrders;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Place;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A quantity that is a form over a row's own numbers: one position's values, how far two stand
 * apart, or what a form of several comes to.
 *
 * <p>What the three share and no other quantity does. Each is its terms weighed by coefficients,
 * so a row is read at it term by term, a line on it runs in a direction over those terms, and the
 * quantity can be taken at another position by moving one of its terms. A quantity that is not a
 * form — how many elements of a container meet something — is read off the row whole, and asked
 * any of these it would have to answer with a form it is not.
 *
 * <p>Sealed over the three, each of which is a {@link BorderQuantity}: what every quantity a border
 * is on answers is asked there, and this is what a reader that needs the form asks.
 */
public sealed interface LinearQuantity extends BorderQuantity
        permits BorderQuantity.OfACoordinate, BorderQuantity.Apart, BorderQuantity.OverAForm {

    /**
     * Every term this quantity is taken of.
     *
     * <p>What a caller moving a quantity to another position has to know it is moving. Read off the
     * arm rather than off the direction the quantity runs in, which is the same list said twice as
     * long as the two agree and one reader's answer the day they do not.
     */
    List<NumericTerm> terms();

    /**
     * The same quantity, with {@code from} taken at {@code to} instead — or null where it is not
     * this quantity's term, or where the move leaves something a quantity cannot be.
     *
     * <p><b>For one name standing at more than one position.</b> A field every case of a sum spreads
     * is one field, so a quantity taken of it is one quantity and it is taken under each case; what
     * moves is where the number is taken, and the comparison that named it is read once and stays
     * one comparison.
     *
     * <p>Answered here rather than assembled by whoever resolved the name, because what has to hold
     * of a quantity is this type's: a distance runs between two positions on orders a value can be
     * counted from one to the other, and a caller building the pair itself would be the second place
     * that has to know it.
     *
     * <p>Where it lands is read off the orders rather than named beside them. What the term is read
     * on and answers at its new position is a fact about that position — it cannot be carried over
     * from where it was — and the reading's answer says which position it is about, so a second
     * argument saying it is a second thing to get right and one this could not refuse: it does not
     * use the name it is given.
     *
     * @param to what the term is read on and answers at its new position, and which position that is
     */
    LinearQuantity movedTo(NumericTerm from, TermOrders to);

    /**
     * The order one position under this quantity is read and written back on, or null where the
     * quantity is not over that position.
     *
     * <p>Asked per position rather than once. A quantity used to answer with the one order every
     * position under it was on, which a coordinate and a line between two positions can do because
     * they have one — and a form was then held to the same, so a form over positions written back
     * differently was no quantity at all.
     *
     * <p>Nothing is asked of the orders beyond each having counts under it. Which positions a form
     * weighs, and with what, is settled by the arithmetic or the operation semantics that produced
     * the form; this layer does not decide that again.
     */
    TermOrders ordersOf(NumericTerm term);

    /** The order that position's values are counted on, which is what its orders answer. Null on
     *  the same reading: a quantity not over the position is over nothing of it. */
    default Carrier carrierOf(NumericTerm term) {
        TermOrders orders = ordersOf(term);
        return orders == null ? null : orders.answered();
    }

    /**
     * What this quantity weighs each of its positions by, as a form over them.
     *
     * <p>The one shape all three are read as, and the reason a reader of a line never asks which of
     * them it is holding. One position's own values are that position weighed once; how far two
     * positions stand apart is their difference; a form is itself. Which way the form runs is part
     * of it — {@code a - b} and {@code b - a} order the rows opposite ways — and how much of the
     * quantity was written is not, so a caller after the quantity itself takes
     * {@link QuantityKey#of}.
     */
    LinearForm<NumericTerm> direction();

    /**
     * What each of this quantity's terms reads as at one row.
     *
     * <p>Every term, whatever came of any of them, and nothing concluded from any of them. Asking
     * them all is how how many elements each position holds is found out, which is what says how
     * many readings of the row there are to try, so a walk that left off as soon as it knew an
     * answer would be choosing the readings — and the answer it knew is not the only one asked of a
     * row, so it is not this walk's to know.
     *
     * <p>Each term on its own order, which is {@link #ordersOf}'s answer and not one order for the
     * quantity: a position written back differently from its neighbour would be read as a value it
     * does not hold, and a date read as a whole number is no number at all.
     *
     * <p>And each asked for what its own number is of — one value where a place answers the term,
     * every value where the term is taken over a run of them. Asked for one either way, a total
     * would be read off whichever element the row's reading happened to pick.
     *
     * <p>Written once for all three, because reading a position is the position's business and not
     * the quantity's shape. What is made of the numbers afterwards is the quantity's, and what is
     * asked of them is the caller's: {@link #valuesOf} hands back the numbers for a caller holding
     * the row against a line the model did not draw, and {@link #standsAt} answers about the line it
     * did.
     */
    default QuantityReading read(Observation observation) {
        Map<TermOrders, WhatATermRead> answers = new LinkedHashMap<>();
        for (NumericTerm term : terms()) {
            TermOrders orders = ordersOf(term);
            WhatATermRead read = switch (term) {
                case NumericTerm.FromOnePosition one ->
                        WhatATermRead.at(orders, observation.at(one.position()));
                case NumericTerm.TakenOver over ->
                        WhatATermRead.over(orders, observation.everyValueAt(over.subjectPath()));
            };
            // One entry per term, which the orders say they are of, so two could only meet where a
            // quantity is taken of one term twice. Refused rather than let the second stand: a
            // reading that kept one of them would answer for a term with what another one read.
            if (answers.put(orders, read) != null) {
                throw new IllegalStateException(
                        "a quantity is taken of each of its terms once, and this names " + orders
                                + " among " + terms());
            }
        }
        return new QuantityReading(answers);
    }

    /**
     * What this quantity's positions hold at the row {@code reading} was made of, or why the row
     * leaves it no value.
     *
     * <p>What stopped a reading is collected over the whole quantity rather than taken from
     * whichever position the walk began with. A row that wrote nothing at one of them leaves this
     * quantity no value there, which is the row's own answer and outranks whatever else was met.
     *
     * <p>The same for all three, because what the numbers are is not the quantity's shape. What they
     * come to under the line the model drew is, and that is {@link #standsAt}.
     *
     * <p>Over this quantity's own terms, and never over the entries the reading happens to hold.
     * What a reading holds is what some quantity read; which of it is this one's to fold is this
     * one's to say, and a fold that took what it was given would answer for one quantity with
     * another's numbers.
     */
    default ValuesAtARow valuesOf(QuantityReading reading) {
        Map<NumericTerm, Place> read = new LinkedHashMap<>();
        Set<ReadingGap> stopped = new LinkedHashSet<>();
        boolean noValue = false;
        for (NumericTerm term : terms()) {
            switch (reading.of(ordersOf(term))) {
                case WhatATermRead.CameToNothing(ReadingGap why) -> stopped.add(why);
                case WhatATermRead.NoNumberOfTheValue _,
                     WhatATermRead.NothingWrittenThere _ -> noValue = true;
                case WhatATermRead.Number(Place value) -> read.put(term, value);
            }
        }
        if (noValue) {
            return ValuesAtARow.NONE_HERE;
        }
        return stopped.isEmpty() ? new ValuesAtARow.Read(read)
                : new ValuesAtARow.CouldNotTell(stopped);
    }

    /** What each of a form's terms is measured on, for a reader of a line rather than of a row. */
    static Map<NumericTerm, Carrier> answeredOn(Map<NumericTerm, TermOrders> orders) {
        Map<NumericTerm, Carrier> out = new LinkedHashMap<>();
        orders.forEach((term, on) -> {
            // Each entry's orders are that position's own. A table whose keys are the right numbers
            // says nothing about which of them each answer came from, and what comes out of here is
            // a number filed under an order, with the term gone.
            on.areOf(term);
            out.put(term, on.answered());
        });
        return Map.copyOf(out);
    }

    /**
     * Whether the row {@code reading} was made of stands at one item of a border on this quantity,
     * or whether it could not be read.
     *
     * <p>Asked of a reading and not of a row, so that a row read once can be asked this and
     * {@link #valuesOf} both, and asked about a second criterion without being read again. What the
     * numbers come to is each quantity's own — a position's value stands on its carrier, a distance
     * is the difference of its ends, a form is its terms added up under their coefficients — and
     * what they were read as is not.
     */
    Stands standsAt(Criterion where, QuantityReading reading);

    /** A form reads one number per term, and stands where those numbers put it. */
    @Override
    default Stands standsAt(Criterion where, Observation row) {
        return standsAt(where, read(row));
    }

    @Override
    default void lookAt(Observation row) {
        read(row);
    }
}
