package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.numeric.Place;
import souther.compiler.observe.ObservedValue;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.List;
import java.util.Optional;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * How many different values the elements meeting a statement hold is told by equality of their
 * observations only where that is the language's sameness, and a value it is not for may be one of
 * the others or another, so it is counted as one that is unread.
 *
 * <p>A decimal observed at two scales is one amount, which counting two of them would not say.
 */
class ValuesCountedAsDifferentAreOnlyThoseWhoseFormIsTheirSamenessTest {

    private static final TermPath ELEMENTS = TermPath.of("xs");
    private static final DecisionSubject.AnInput VALUE =
            new DecisionSubject.AnInput(ELEMENTS.element());

    private static final Proposition ANY = new Proposition.Present(VALUE, true);

    @Test
    void valuesThatAreToldAreCountedOnceEach() {
        assertEquals(new AStatementAtARow.HowManyAtARow(2, 0, Set.of()),
                differentIn(new ObservedValue.Text("A"), new ObservedValue.Text("A"),
                        new ObservedValue.Text("B")));
    }

    @Test
    void aValueWhoseSamenessIsNotToldIsCountedAsOneThatCouldBeAnother() {
        assertEquals(new AStatementAtARow.HowManyAtARow(1, 2, Set.of(ReadingGap.SAMENESS_NOT_TOLD)),
                differentIn(new ObservedValue.Text("A"),
                        new ObservedValue.Decimal(new BigDecimal("1.0")),
                        new ObservedValue.Decimal(new BigDecimal("1.00"))));
    }

    private static AStatementAtARow.HowManyAtARow differentIn(ObservedValue... held) {
        return AStatementAtARow.of(ANY, "f", null).howManyIn(ELEMENTS,
                Optional.of(new Quantity.TheValue.AtAPlace(VALUE)), Optional.empty(),
                new Elements(List.of(held)));
    }

    /** A row whose container holds one element for each value. */
    private record Elements(List<ObservedValue> held) implements BorderQuantity.Observation {

        @Override
        public WalkResult<ObservationAtPoint> at(TermPath path) {
            return WalkResult.couldNotWalk();
        }

        @Override
        public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
            throw new AssertionError("a count of different values reads one value of each element");
        }

        @Override
        public Place fixedAt(NumericTerm term) {
            return null;
        }

        @Override
        public WalkResult<List<BorderQuantity.Observation>> eachElementOf(TermPath container) {
            return WalkResult.reached(held.stream()
                    .<BorderQuantity.Observation>map(Element::new).toList());
        }
    }

    /** One element, holding the value at the place the element is read at. */
    private record Element(ObservedValue value) implements BorderQuantity.Observation {

        @Override
        public WalkResult<ObservationAtPoint> at(TermPath path) {
            return WalkResult.reached(new ObservationAtPoint.Value(value));
        }

        @Override
        public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
            throw new AssertionError("a count of different values reads one value of each element");
        }

        @Override
        public Place fixedAt(NumericTerm term) {
            return null;
        }

        @Override
        public WalkResult<List<BorderQuantity.Observation>> eachElementOf(TermPath container) {
            return WalkResult.couldNotWalk();
        }
    }
}
