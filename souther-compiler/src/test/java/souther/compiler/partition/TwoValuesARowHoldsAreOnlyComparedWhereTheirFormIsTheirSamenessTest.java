package souther.compiler.partition;

import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.numeric.Place;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;
import souther.compiler.values.Operand;

import org.junit.jupiter.api.Test;

import java.math.BigDecimal;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * Two values a row holds are said to be the same, or not, only where the form of their observation
 * is their sameness, and otherwise are not read.
 *
 * <p>An observation says what was there and not what the declaration of its type makes of it: a
 * decimal observed at two scales is one amount, and a sequence is a list or a set by where it
 * stands. Compared as records they would be told apart, so what is said of them is that a row does
 * not say, and never a verdict that depends on how they were written.
 */
class TwoValuesARowHoldsAreOnlyComparedWhereTheirFormIsTheirSamenessTest {

    private static final TermPath ONE = TermPath.of("a");
    private static final TermPath OTHER = TermPath.of("b");

    private static final TypeSymbol CODE = TypeSymbols.declared(new TypeKey("probe", "Code"));

    private static final AStatementAtARow.Answer NOT_TOLD = new AStatementAtARow.Answer.CouldNotTell(
            Set.of(ReadingGap.SAMENESS_NOT_TOLD));

    @Test
    void valuesWhoseFormIsTheirSamenessAreSaidToBeTheSameOrNot() {
        assertBoth(AStatementAtARow.Answer.HOLDS, AStatementAtARow.Answer.FAILS,
                text("A"), text("A"));
        assertBoth(AStatementAtARow.Answer.FAILS, AStatementAtARow.Answer.HOLDS,
                text("A"), text("B"));
        assertBoth(AStatementAtARow.Answer.HOLDS, AStatementAtARow.Answer.FAILS,
                new ObservedValue.Integer(1), new ObservedValue.Integer(1));
        assertBoth(AStatementAtARow.Answer.FAILS, AStatementAtARow.Answer.HOLDS,
                new ObservedValue.Integer(1), new ObservedValue.Integer(2));
    }

    @Test
    void aNewtypeIsTheSameWhereWhatItWrapsIs() {
        assertBoth(AStatementAtARow.Answer.HOLDS, AStatementAtARow.Answer.FAILS,
                wrapped(text("A")), wrapped(text("A")));
        assertBoth(AStatementAtARow.Answer.FAILS, AStatementAtARow.Answer.HOLDS,
                wrapped(text("A")), wrapped(text("B")));
    }

    @Test
    void aDecimalAtTwoScalesIsNotToldAndNeitherIsTheSameScale() {
        assertBoth(NOT_TOLD, NOT_TOLD, decimal("1.0"), decimal("1.00"));
        assertBoth(NOT_TOLD, NOT_TOLD, decimal("1.0"), decimal("1.0"));
    }

    @Test
    void aSequenceIsNotToldWhetherItIsAListOrASet() {
        ObservedValue oneThenTwo = sequence(new ObservedValue.Integer(1), new ObservedValue.Integer(2));
        ObservedValue twoThenOne = sequence(new ObservedValue.Integer(2), new ObservedValue.Integer(1));

        assertBoth(NOT_TOLD, NOT_TOLD, oneThenTwo, twoThenOne);
        assertBoth(NOT_TOLD, NOT_TOLD, oneThenTwo, oneThenTwo);
    }

    @Test
    void aConstructionHoldingOneIsNotToldEither() {
        assertBoth(NOT_TOLD, NOT_TOLD, wrapped(decimal("1.0")), wrapped(decimal("1.00")));
        assertBoth(NOT_TOLD, NOT_TOLD, wrapped(sequence(text("A"))), wrapped(sequence(text("A"))));
    }

    @Test
    void oneSideOutsideWhatIsToldIsEnoughToNotTell() {
        assertBoth(NOT_TOLD, NOT_TOLD, text("1"), decimal("1"));
    }

    @Test
    void whatWasNotReadInFullIsSaidAsThatAndNotAsNotBeingToldTheSameness() {
        ObservedValue stopped = new ObservedValue.Unknown("nothing read it");
        AStatementAtARow.Answer why = new AStatementAtARow.Answer.CouldNotTell(
                Set.of(ReadingGap.ofAComparisonOf(stopped)));

        assertBoth(why, why, stopped, text("A"));
        assertBoth(why, why, wrapped(stopped), wrapped(text("A")));
    }

    private static void assertBoth(AStatementAtARow.Answer same, AStatementAtARow.Answer denied,
                                   ObservedValue one, ObservedValue other) {
        Proposition stated = new Proposition.SameValue(new DecisionSubject.AnInput(ONE),
                new Operand.At<>(new DecisionSubject.AnInput(OTHER)), true);
        Map<TermPath, ObservationAtPoint> row = Map.of(
                ONE, new ObservationAtPoint.Value(one), OTHER, new ObservationAtPoint.Value(other));

        assertEquals(same, at(stated, row), "as stated: " + one + " and " + other);
        assertEquals(denied, at(stated.denied(), row), "denied: " + one + " and " + other);
    }

    private static ObservedValue text(String value) {
        return new ObservedValue.Text(value);
    }

    private static ObservedValue decimal(String value) {
        return new ObservedValue.Decimal(new BigDecimal(value));
    }

    private static ObservedValue wrapped(ObservedValue value) {
        return new ObservedValue.Constructed(CODE, Map.of("value", value));
    }

    private static ObservedValue sequence(ObservedValue... elements) {
        return new ObservedValue.Sequence(List.of(elements));
    }

    private static AStatementAtARow.Answer at(Proposition stated,
                                              Map<TermPath, ObservationAtPoint> walked) {
        return AStatementAtARow.of(stated, "f", null).at(new AnObservationOfAForm() {

            @Override
            public Place fixedAt(NumericTerm term) {
                return null;
            }

            @Override
            public WalkResult<ObservationAtPoint> at(TermPath path) {
                ObservationAtPoint there = walked.get(path);
                return there == null ? WalkResult.couldNotWalk() : WalkResult.reached(there);
            }

            @Override
            public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
                throw new AssertionError("a sameness of two positions is not read over a run");
            }
        });
    }
}
