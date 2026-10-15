package souther.compiler.inputs;

import souther.compiler.check.Carrier;
import souther.compiler.numeric.Place;
import souther.compiler.values.Value;
import souther.compiler.values.ValueSet;

import java.util.ArrayList;
import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Every value a position's rules admit, each with the number every term asked of it reads of that
 * value.
 *
 * <p>The relation and not its projections. Two numbers taken of one position are two readings of
 * one value, and which value comes to which pair is what a set of the numbers each comes to leaves
 * out: {@code " a"}, {@code "bb"} and {@code "c"} come to the lengths {@code {1, 2}} and to the
 * trimmed lengths {@code {1, 2}}, and only three of the four pairs those make are pairs a value
 * comes to. So a reader asking several numbers of one row together asks them of one value here,
 * and the set one number comes to on its own ({@link SearchRegion#heldAt}) is this read through
 * that number alone.
 *
 * <p>Only ever as wide as what the rules admit. Every value a row can hold at the position is one
 * of these, so a reading no value comes to is one no row comes to; a value here is not shown to be
 * one a row can hold.
 *
 * @param each every value the position admits, with what each term reads of it, in the order the
 *             values were named
 */
public record ReadingsOfEachValue(List<ReadingsOfEachValue.Read> each) {

    public ReadingsOfEachValue {
        each = List.copyOf(each);
    }

    /**
     * One value the position admits and the number each term reads of it.
     *
     * @param value   the value, as a rule names it
     * @param numbers what each term reads of it, on the order the term is answered on
     */
    public record Read(Value value, Map<NumericTerm, Place> numbers) {

        public Read {
            numbers = Collections.unmodifiableMap(new LinkedHashMap<>(numbers));
        }
    }

    /**
     * Each value of {@code admitted} read through every one of {@code orders} — or null where
     * {@code admitted} is not finitely many values, where the terms are not all of one position, or
     * where a value is read as no number of one of them.
     *
     * <p>Null and not a shorter list. A value left out would be a value no reading reaches, and a
     * reader holding the rest would take a number that value comes to for one nothing comes to.
     *
     * @param orders the orders of each term asked, every one of them taken of one position's value
     */
    static ReadingsOfEachValue of(ValueSet admitted, List<TermOrders> orders) {
        if (orders.isEmpty() || !(admitted instanceof ValueSet.Finite finite)) {
            return null;
        }
        NumericTerm.FromOnePosition first = orders.getFirst().term().atOnePosition();
        for (TermOrders each : orders) {
            NumericTerm.FromOnePosition here = each.term().atOnePosition();
            if (first == null || here == null || !here.position().equals(first.position())) {
                return null;
            }
        }
        List<Read> out = new ArrayList<>();
        for (Value value : finite.values()) {
            Map<NumericTerm, Place> numbers = new LinkedHashMap<>();
            for (TermOrders each : orders) {
                if (!(each.readOf(value) instanceof NumericTerm.Reading.Number(Place number))) {
                    return null;
                }
                numbers.put(each.term(), number);
            }
            out.add(new Read(value, numbers));
        }
        return new ReadingsOfEachValue(out);
    }

    /**
     * The numbers {@code orders}' term comes to of these values, as a set of values on the order it
     * is answered on — or every value where one of them is a number that order writes no value
     * for.
     */
    ValueSet comeTo(TermOrders orders) {
        Carrier answered = orders.answered();
        if (answered == null) {
            return ValueSet.ANY;
        }
        Set<Value> numbers = new LinkedHashSet<>();
        for (Read read : each) {
            Value comesTo = answered.valueAt(read.numbers().get(orders.term()));
            if (comesTo == null) {
                return ValueSet.ANY;
            }
            numbers.add(comesTo);
        }
        return ValueSet.oneOf(numbers);
    }
}
