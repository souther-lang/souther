package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.inputs.Case;
import souther.compiler.inputs.CasesLeft;
import souther.compiler.inputs.Refinement;
import souther.compiler.inputs.TermPath;
import souther.compiler.meaning.DecisionSubject;
import souther.compiler.meaning.Proposition;
import souther.compiler.observe.ObservedValue;
import souther.compiler.types.TypeKey;
import souther.compiler.types.TypeSymbol;
import souther.compiler.types.TypeSymbols;

import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a position is one of some cases of a sum is read off the case a row wrote there.
 *
 * <p>A row names the case it put at a position, a case carrying nothing and a case with fields
 * alike, so a statement joining a relation with the case of a position is one a row can be asked,
 * and a line it draws decides where the row is in that case. A value no declaration names is no
 * case the row is in or out of, and is not read.
 */
class WhatARowPutAtAPositionAnswersWhichCaseItIsTest {

    private static final TermPath STAGE = TermPath.of("s");

    private static final TypeSymbol HOT = TypeSymbols.declared(new TypeKey("probe", "Hot"));
    private static final TypeSymbol WARM = TypeSymbols.declared(new TypeKey("probe", "Warm"));
    private static final TypeSymbol COLD = TypeSymbols.declared(new TypeKey("probe", "Cold"));

    private static final Proposition HOT_HOLDS = inCases(List.of(HOT));
    private static final Proposition WARM_OR_COLD = inCases(List.of(WARM, COLD));

    @Test
    void aCaseOfThePositionIsAStatementARowAnswers() {
        assertTrue(AStatementAtARow.askable(HOT_HOLDS));
        assertTrue(AStatementAtARow.askable(WARM_OR_COLD.denied()));
        assertTrue(AStatementAtARow.askable(new Proposition.All(List.of(HOT_HOLDS,
                new Proposition.Truth(new DecisionSubject.AnInput(STAGE.then("open")), true)))));
    }

    /** Whether an optional holds a value is asked as whether it is present, and not as a case. */
    @Test
    void aCaseOfAnOptionalIsNoCaseOfASum() {
        assertFalse(AStatementAtARow.askable(new Proposition.InCases(
                new DecisionSubject.AnInput(STAGE),
                CasesLeft.of(Refinement.of(new Case.Presence(true))), true)));
    }

    @Test
    void aCaseHoldsWhereTheRowPutThatCaseThere() {
        assertEquals(AStatementAtARow.Answer.HOLDS,
                at(HOT_HOLDS, new ObservedValue.Unit(HOT)));
        assertEquals(AStatementAtARow.Answer.FAILS,
                at(HOT_HOLDS, new ObservedValue.Unit(WARM)));
        assertEquals(AStatementAtARow.Answer.HOLDS,
                at(HOT_HOLDS.denied(), new ObservedValue.Unit(WARM)));
    }

    /** Several cases hold where the row put any one of them, and the rest fail. */
    @Test
    void severalCasesHoldWhereTheRowPutAnyOfThem() {
        assertEquals(AStatementAtARow.Answer.HOLDS,
                at(WARM_OR_COLD, new ObservedValue.Unit(WARM)));
        assertEquals(AStatementAtARow.Answer.HOLDS,
                at(WARM_OR_COLD, new ObservedValue.Unit(COLD)));
        assertEquals(AStatementAtARow.Answer.FAILS,
                at(WARM_OR_COLD, new ObservedValue.Unit(HOT)));
    }

    /** A case with fields is the case it was built as, read the same way. */
    @Test
    void aCaseWithFieldsIsTheCaseItWasBuiltAs() {
        Map<String, ObservedValue> fields = ObservedValue.fields();
        fields.put("since", new ObservedValue.Integer(3));
        assertEquals(AStatementAtARow.Answer.HOLDS,
                at(HOT_HOLDS, new ObservedValue.Constructed(HOT, fields)));
        assertEquals(AStatementAtARow.Answer.FAILS,
                at(HOT_HOLDS, new ObservedValue.Constructed(WARM, fields)));
    }

    /**
     * A value no declaration names is not read, whichever way the case is asked: it is not out of
     * the case, and denying the case does not make it in.
     */
    @Test
    void aValueOfNoDeclarationIsNotRead() {
        AStatementAtARow.Answer notRead =
                new AStatementAtARow.Answer.CouldNotTell(Set.of(ReadingGap.NO_VALUE));
        assertEquals(notRead, at(HOT_HOLDS, new ObservedValue.Integer(1)));
        assertEquals(notRead, at(HOT_HOLDS.denied(), new ObservedValue.Integer(1)));
    }

    private static Proposition inCases(List<TypeSymbol> leaves) {
        return new Proposition.InCases(new DecisionSubject.AnInput(STAGE),
                CasesLeft.ofEach(leaves.stream()
                        .map(leaf -> Refinement.of(new Case.SumCase(leaf, true))).toList()),
                true);
    }

    private static AStatementAtARow.Answer at(Proposition stated, ObservedValue wrote) {
        return AStatementAtARow.of(stated, "f", null).at(new AnObservationOfAForm() {

            @Override
            public WalkResult<ObservationAtPoint> at(TermPath path) {
                return path.equals(STAGE)
                        ? WalkResult.reached(new ObservationAtPoint.Value(wrote))
                        : WalkResult.couldNotWalk();
            }

            @Override
            public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
                throw new AssertionError("a case of one position is not read over a run");
            }
        });
    }
}
