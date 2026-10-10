package souther.compiler.inputs;

import org.junit.jupiter.api.Test;

import souther.compiler.check.Carrier;
import souther.compiler.check.DeclarationAccess;
import souther.compiler.numeric.Count;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.Type;

import java.math.BigDecimal;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertInstanceOf;

/**
 * How often a value occurs among the values beside it is how often the order the place stands on
 * puts a value at the one place, and not how often an observation is written the same way: a
 * decimal is the amount it stands for however many places it is written to, and a value the order
 * has no place for is no number here rather than one of its own.
 */
class HowOftenAValueOccursIsCountedByTheOrderItStandsOnTest {

    private static final NumericTerm.Multiplicity AMONG = NumericTerm.Multiplicity.of(
            TermPath.of("xs"), TermPath.of("xs").element());

    private static ObservedValue decimal(String written) {
        return new ObservedValue.Decimal(new BigDecimal(written));
    }

    private static NumericTerm.Reading read(Carrier on, ObservedValue own,
                                            List<ObservedValue> every) {
        return TermOrdersFixtures.itself(AMONG, on).readAmong(own, every);
    }

    @Test
    void twoDecimalsOfOneAmountAreOneValueWhateverScaleEachIsWrittenTo() {
        Carrier decimals = Carrier.ofValue(Type.Prim.DECIMAL, DeclarationAccess.NONE);
        List<ObservedValue> every = List.of(decimal("1.0"), decimal("1.00"), decimal("2.0"));
        assertEquals(new NumericTerm.Reading.Number(Count.of(2)),
                read(decimals, decimal("1.0"), every));
        assertEquals(new NumericTerm.Reading.Number(Count.of(2)),
                read(decimals, decimal("1.00"), every));
        assertEquals(new NumericTerm.Reading.Number(Count.of(1)),
                read(decimals, decimal("2.0"), every));
    }

    @Test
    void textsAreTheSameWhereTheyAreWrittenAlike() {
        List<ObservedValue> every = List.of(new ObservedValue.Text("a"),
                new ObservedValue.Text("b"), new ObservedValue.Text("a"));
        assertEquals(new NumericTerm.Reading.Number(Count.of(2)),
                read(Carrier.TEXT, new ObservedValue.Text("a"), every));
    }

    @Test
    void aValueTheOrderHasNoPlaceForIsNoNumber() {
        ObservedValue parts = new ObservedValue.Sequence(List.of(new ObservedValue.Text("a")));
        assertInstanceOf(NumericTerm.Reading.NotNumber.class,
                read(Carrier.TEXT, parts, List.of(parts, parts)));
    }

    @Test
    void aValueThatWasNotReadIsNotCountedAsAnotherOrTheSame() {
        List<ObservedValue> every = List.of(new ObservedValue.Text("a"),
                new ObservedValue.Truncated());
        assertInstanceOf(NumericTerm.Reading.Missing.class,
                read(Carrier.TEXT, new ObservedValue.Text("a"), every));
    }
}
