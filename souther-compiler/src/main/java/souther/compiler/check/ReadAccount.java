package souther.compiler.check;

import souther.compiler.numeric.NumericDomain;
import souther.compiler.values.ConjoinedAdmissibleValues;
import souther.compiler.values.ValueSet;

/**
 * What the reading of a value's rules says of a place beyond its range: the order its numbers are
 * worked out in, and which values the rules leave it.
 *
 * <p>The order is asked of what named the place and not of the interval algebra, which is told it
 * only once the reading is done.
 *
 * @param terms  what knows the order each place's numbers run on
 * @param values the values the rules leave each place, as the reading ended
 */
record ReadAccount(Terms terms, ConjoinedAdmissibleValues<FactSubject> values)
        implements ComputedNumbers.Account {

    @Override
    public NumericDomain.Bounds orderOf(FactSubject place) {
        Carrier order = terms.carrierOfTerm(place.identity());
        return order == null ? null : order.whereItStops();
    }

    @Override
    public boolean shownExact(FactSubject place) {
        return values.projectionExactAt(place);
    }

    @Override
    public boolean restrictsNothingBesideItsRange(FactSubject place) {
        return shownExact(place) && values.at(place).equals(ValueSet.ANY);
    }
}
