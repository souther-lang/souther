package souther.compiler.check;

import souther.compiler.numeric.NumericDomain;
import souther.compiler.values.ConjoinedAdmissibleValues;
import souther.compiler.values.ValueSet;

/**
 * What the reading of a value's rules says of a place beyond its range: the order its numbers are
 * worked out in, and which values the rules leave it.
 *
 * @param values the values the rules leave each place, as the reading ended
 * @param terms  what knows the order each place's numbers run on
 */
record ReadAccount(ConjoinedAdmissibleValues<FactSubject> values, Terms terms)
        implements ComputedNumbers.Account {

    @Override
    public NumericDomain.Bounds orderOf(FactSubject place) {
        Carrier order = terms.carrierOf(place);
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
