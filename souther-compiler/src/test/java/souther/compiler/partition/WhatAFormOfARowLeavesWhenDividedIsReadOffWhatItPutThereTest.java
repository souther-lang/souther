package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.DefaultStdlib;
import souther.compiler.carrier.Membership;
import souther.compiler.check.RuleReadingContext;
import souther.compiler.check.RuleReadingSource;
import souther.compiler.check.RuleReadings;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeCardinality;
import souther.compiler.inputs.InputDomain;
import souther.compiler.inputs.NumericTerm;
import souther.compiler.inputs.Quantities;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.Proposition;
import souther.compiler.meaning.Quantity;
import souther.compiler.meaning.Relation;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Rel;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import java.math.BigInteger;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a division by a written number leaves of a form of a row's numbers is read off what the row
 * put at each, the way a line on the remainder reads a row.
 *
 * <p>So a statement holding a relation on a remainder is one a row can be asked. A row that wrote
 * nothing at a number of the form has no remainder, so the relation and its denial both fail
 * there; a row the walk did not reach at a number is not read, which is neither.
 */
class WhatAFormOfARowLeavesWhenDividedIsReadOffWhatItPutThereTest {

    private static final RuleReadingSource RULES =
            RuleReadings.ofNoClauseFiled(Symbols.none(DefaultStdlib.get()));

    private static final TermPath X = TermPath.of("x");
    private static final TermPath Y = TermPath.of("y");

    /** {@code floorMod(x + y, 11) <= 7}, the denial of being above seven. */
    private static final Proposition AT_MOST_SEVEN =
            against(remainder(1, 1, 0), ExactRatio.of(-7), Rel.GT).denied();

    /** {@code floorMod(3 * x + y + 5, 11) == 7}. */
    private static final Proposition SEVEN_OF_A_WEIGHTED_FORM =
            against(remainder(3, 1, 5), ExactRatio.of(-7), Rel.EQ);

    /** {@code floorMod(x + y, 11) == 10}. */
    private static final Proposition TEN = against(remainder(1, 1, 0), ExactRatio.of(-10), Rel.EQ);

    @Test
    void aRelationOnARemainderOfAFormIsAStatementARowAnswers() {
        assertTrue(AStatementAtARow.askable(AT_MOST_SEVEN));
        assertTrue(AStatementAtARow.askable(AT_MOST_SEVEN.denied()));
    }

    @Test
    void itHoldsWhereTheFormLeavesWhatItStates() {
        assertEquals(AStatementAtARow.Answer.HOLDS, at(AT_MOST_SEVEN, 3, 4));
        assertEquals(AStatementAtARow.Answer.FAILS, at(AT_MOST_SEVEN, 3, 5));
        assertEquals(AStatementAtARow.Answer.HOLDS, at(AT_MOST_SEVEN.denied(), 3, 5));
        assertEquals(AStatementAtARow.Answer.FAILS, at(AT_MOST_SEVEN.denied(), 3, 4));
    }

    @Test
    void theFormIsWeighedAndMovedByItsConstantBeforeItIsDivided() {
        assertEquals(AStatementAtARow.Answer.HOLDS, at(SEVEN_OF_A_WEIGHTED_FORM, 0, 2));
        assertEquals(AStatementAtARow.Answer.FAILS, at(SEVEN_OF_A_WEIGHTED_FORM, 0, 3));
    }

    /** The remainder takes the divisor's sign: minus one leaves ten, and not minus one. */
    @Test
    void aNegativeFormLeavesWhatTheMathematicsOfAFloorRemainderDoes() {
        assertEquals(AStatementAtARow.Answer.HOLDS, at(TEN, -1, 0));
        assertEquals(AStatementAtARow.Answer.HOLDS, at(TEN, -12, 0));
        assertEquals(AStatementAtARow.Answer.FAILS, at(TEN, 10, 1));
    }

    /** A row that wrote nothing at a number has no remainder: it is on neither side. */
    @Test
    void aNumberTheRowWroteNothingAtIsOnNeitherSide() {
        assertEquals(AStatementAtARow.Answer.FAILS, atNothing(AT_MOST_SEVEN));
        assertEquals(AStatementAtARow.Answer.FAILS, atNothing(AT_MOST_SEVEN.denied()));
    }

    /** What the walk did not reach is not read, which is not the same as nothing being there. */
    @Test
    void aNumberTheRowDoesNotSayIsNotRead() {
        assertTrue(AStatementAtARow.of(AT_MOST_SEVEN, "f", quantities()).at(
                row(Map.of(X, new ObservationAtPoint.Value(new ObservedValue.Integer(3)))))
                instanceof AStatementAtARow.Answer.CouldNotTell);
    }

    /** Over a number of the form the relation turns at no place: the remainder comes round. */
    @Test
    void itTurnsAtNoPlaceOfAnyNumberOfTheForm() {
        AStatementAtARow read = AStatementAtARow.of(AT_MOST_SEVEN, "f", quantities());
        NumericTerm x = new NumericTerm.ValueOf(X);
        assertEquals(null, read.turnsAt(x, Map.of()));
        assertEquals(null, read.placesTurnedAt(x, Map.of()));
    }

    /** {@code weight * x + y + constant}, by eleven. */
    private static Quantity.RemainderOfADividend remainder(long onX, long onY, long constant) {
        return new Quantity.RemainderOfADividend(ValueName.Stdlib.operation("Int", "floorMod"),
                new LinearForm<>(ExactRatio.of(constant), Map.of(
                        new NumericTerm.ValueOf(X), ExactRatio.of(onX),
                        new NumericTerm.ValueOf(Y), ExactRatio.of(onY))),
                BigInteger.valueOf(11));
    }

    private static Proposition against(Quantity.RemainderOfADividend remainder,
                                       ExactRatio constant, Rel rel) {
        return new Proposition.Compared(new Relation.Affine(
                new LinearForm<>(constant, Map.of(remainder, ExactRatio.ONE)), rel), true);
    }

    private static AStatementAtARow.Answer at(Proposition stated, long x, long y) {
        return AStatementAtARow.of(stated, "f", quantities()).at(row(Map.of(
                X, new ObservationAtPoint.Value(new ObservedValue.Integer(x)),
                Y, new ObservationAtPoint.Value(new ObservedValue.Integer(y)))));
    }

    private static AStatementAtARow.Answer atNothing(Proposition stated) {
        return AStatementAtARow.of(stated, "f", quantities()).at(row(Map.of(
                X, new ObservationAtPoint.WroteNothing(),
                Y, new ObservationAtPoint.WroteNothing())));
    }

    /** A reading of an input taking two whole numbers, {@code x} and {@code y}. */
    private static Quantities quantities() {
        RuleReadingContext reading =
                RuleReadingContext.unshared(RULES, ReadAs.THE_COMPILATION_DOES);
        return InputDomain.of(
                List.of(new InputDomain.Parameter("x", null, Type.INT),
                        new InputDomain.Parameter("y", null, Type.INT)),
                reading, TypeCardinality.Counts.workedOutIn(reading),
                Membership.none()).quantities(RULES);
    }

    private static BorderQuantity.Observation row(Map<TermPath, ObservationAtPoint> wrote) {
        Map<TermPath, ObservationAtPoint> at = new LinkedHashMap<>(wrote);
        return new AnObservationOfAForm() {

            @Override
            public WalkResult<ObservationAtPoint> at(TermPath path) {
                ObservationAtPoint here = at.get(path);
                return here == null ? WalkResult.couldNotWalk() : WalkResult.reached(here);
            }

            @Override
            public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
                throw new AssertionError("a number of one position is not read over a run");
            }
        };
    }
}
