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
import souther.compiler.numeric.Count;
import souther.compiler.numeric.ExactRatio;
import souther.compiler.numeric.LinearForm;
import souther.compiler.numeric.Place;
import souther.compiler.numeric.Rel;
import souther.compiler.observe.ObservedValue;
import souther.compiler.query.ReadAs;
import souther.compiler.types.Type;

import java.util.List;
import java.util.Map;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What two whole numbers of a row come to multiplied is read off what the row put at each, the way
 * a line on the product reads a row.
 *
 * <p>So a statement holding a relation on a product is one a row can be asked, and a line among
 * several decides where a row's own numbers say it does. A row whose product passes where the type
 * stops has none: the run stops before it compares, and the row is on neither side, so the
 * relation and its denial both fail there.
 */
class WhatTwoNumbersOfARowComeToMultipliedIsReadOffWhatItPutThereTest {

    private static final RuleReadingSource RULES =
            RuleReadings.ofNoClauseFiled(Symbols.none(DefaultStdlib.get()));

    private static final TermPath A = TermPath.of("a");
    private static final TermPath B = TermPath.of("b");

    /** {@code a * b > 3}. */
    private static final Proposition ABOVE_THREE = new Proposition.Compared(new Relation.Affine(
            new LinearForm<>(ExactRatio.of(-3), Map.of(new Quantity.ProductOfTwo(
                    new NumericTerm.ValueOf(A), new NumericTerm.ValueOf(B)), ExactRatio.ONE)),
            Rel.GT), true);

    @Test
    void aRelationOnAProductIsAStatementARowAnswers() {
        assertTrue(AStatementAtARow.askable(ABOVE_THREE));
        assertTrue(AStatementAtARow.askable(ABOVE_THREE.denied()));
    }

    @Test
    void itHoldsWhereTheTwoNumbersMultiplyToWhatItStates() {
        assertEquals(AStatementAtARow.Answer.HOLDS, at(ABOVE_THREE, 2, 2));
        assertEquals(AStatementAtARow.Answer.FAILS, at(ABOVE_THREE, 3, 1));
        assertEquals(AStatementAtARow.Answer.HOLDS, at(ABOVE_THREE.denied(), 3, 1));
        assertEquals(AStatementAtARow.Answer.FAILS, at(ABOVE_THREE.denied(), -2, -2));
    }

    @Test
    void aProductPastWhereTheTypeStopsIsOnNeitherSide() {
        assertEquals(AStatementAtARow.Answer.FAILS, at(ABOVE_THREE, Long.MAX_VALUE / 2, 4));
        assertEquals(AStatementAtARow.Answer.FAILS,
                at(ABOVE_THREE.denied(), Long.MAX_VALUE / 2, 4));
    }

    /** What the walk did not reach is not read. */
    @Test
    void aFactorTheRowDoesNotSayIsNotRead() {
        assertTrue(AStatementAtARow.of(ABOVE_THREE, "f", quantities()).at(row(Map.of(
                A, new ObservedValue.Integer(2))))
                instanceof AStatementAtARow.Answer.CouldNotTell);
    }

    /**
     * Over one factor, with the other where a row put it, the relation turns at the level over the
     * other and where the product passes an end of the type; with the other at nought it is nought
     * and turns nowhere.
     */
    @Test
    void itTurnsOverOneFactorWhereTheOtherPutsTheLevel() {
        AStatementAtARow read = AStatementAtARow.of(ABOVE_THREE, "f", quantities());
        NumericTerm a = new NumericTerm.ValueOf(A);
        NumericTerm b = new NumericTerm.ValueOf(B);
        assertEquals(List.of(ExactRatio.of(3).dividedBy(ExactRatio.of(2)).orNull(),
                        ExactRatio.of(Long.MIN_VALUE).dividedBy(ExactRatio.of(2)).orNull(),
                        ExactRatio.of(Long.MAX_VALUE).dividedBy(ExactRatio.of(2)).orNull()),
                read.turnsAt(a, Map.of(b, place(2))));
        assertEquals(List.of(), read.turnsAt(a, Map.of(b, place(0))));
        assertEquals(null, read.turnsAt(a, Map.of()));
    }

    private static Place place(long at) {
        return Count.of(at);
    }

    private static AStatementAtARow.Answer at(Proposition stated, long a, long b) {
        return AStatementAtARow.of(stated, "f", quantities()).at(row(Map.of(
                A, new ObservedValue.Integer(a), B, new ObservedValue.Integer(b))));
    }

    /** A reading of an input taking two whole numbers, {@code a} and {@code b}. */
    private static Quantities quantities() {
        RuleReadingContext reading =
                RuleReadingContext.unshared(RULES, ReadAs.THE_COMPILATION_DOES);
        return InputDomain.of(
                List.of(new InputDomain.Parameter("a", null, Type.INT),
                        new InputDomain.Parameter("b", null, Type.INT)),
                reading, TypeCardinality.Counts.workedOutIn(reading),
                Membership.none()).quantities(RULES);
    }

    private static BorderQuantity.Observation row(Map<TermPath, ObservedValue> wrote) {
        return new AnObservationOfAForm() {

            @Override
            public WalkResult<ObservationAtPoint> at(TermPath path) {
                ObservedValue value = wrote.get(path);
                return value == null ? WalkResult.couldNotWalk()
                        : WalkResult.reached(new ObservationAtPoint.Value(value));
            }

            @Override
            public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
                throw new AssertionError("a number of one position is not read over a run");
            }
        };
    }
}
