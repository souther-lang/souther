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

import java.util.Arrays;
import java.util.List;
import java.util.Map;
import java.util.Set;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * Whether a position is one of some cases of a sum is whether the walk into a row reaches the value
 * there at the position narrowed to them.
 *
 * <p>A statement joining a relation with the case of a position is one a row can be asked, and a
 * line it draws decides where the row is in that case. Which case a value is, under whatever names
 * the position wears, is the walk's to say, as it is for every narrowed position; this reads the
 * walk's answer. What the walk did not reach is not read.
 */
class WhatARowPutAtAPositionAnswersWhichCaseItIsTest {

    private static final TermPath STAGE = TermPath.of("s");

    private static final TypeSymbol HOT = TypeSymbols.declared(new TypeKey("probe", "Hot"));
    private static final TypeSymbol WARM = TypeSymbols.declared(new TypeKey("probe", "Warm"));

    private static final CasesLeft ONLY_HOT = casesOf(HOT);
    private static final Proposition HOT_HOLDS =
            new Proposition.InCases(new DecisionSubject.AnInput(STAGE), ONLY_HOT, true);

    private static final ObservedValue A_VALUE = new ObservedValue.Unit(HOT);

    @Test
    void aCaseOfThePositionIsAStatementARowAnswers() {
        assertTrue(AStatementAtARow.askable(HOT_HOLDS));
        assertTrue(AStatementAtARow.askable(new Proposition.InCases(
                new DecisionSubject.AnInput(STAGE), casesOf(HOT, WARM), false)));
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

    /** Holding where the narrowed walk reaches the value, and the other way round denied. */
    @Test
    void aCaseHoldsWhereTheNarrowedWalkReachesTheValue() {
        Map<TermPath, ObservationAtPoint> reached = Map.of(
                STAGE, new ObservationAtPoint.Value(A_VALUE),
                STAGE.refine(ONLY_HOT), new ObservationAtPoint.Value(A_VALUE));
        assertEquals(AStatementAtARow.Answer.HOLDS, at(HOT_HOLDS, reached));
        assertEquals(AStatementAtARow.Answer.FAILS, at(HOT_HOLDS.denied(), reached));
    }

    /** Failing where the value is there and the narrowed walk reaches nothing. */
    @Test
    void aCaseFailsWhereTheNarrowedWalkReachesNothing() {
        Map<TermPath, ObservationAtPoint> elsewhere = Map.of(
                STAGE, new ObservationAtPoint.Value(A_VALUE),
                STAGE.refine(ONLY_HOT), ObservationAtPoint.WROTE_NOTHING);
        assertEquals(AStatementAtARow.Answer.FAILS, at(HOT_HOLDS, elsewhere));
        assertEquals(AStatementAtARow.Answer.HOLDS, at(HOT_HOLDS.denied(), elsewhere));
    }

    /**
     * What the walk did not reach is not read, either way the case is asked, whether at the
     * position or at the position narrowed.
     */
    @Test
    void whatTheWalkDoesNotReachIsNotRead() {
        AStatementAtARow.Answer notWalked =
                new AStatementAtARow.Answer.CouldNotTell(Set.of(ReadingGap.COULD_NOT_WALK));
        assertEquals(notWalked, at(HOT_HOLDS, Map.of()));
        Map<TermPath, ObservationAtPoint> notNarrowed =
                Map.of(STAGE, new ObservationAtPoint.Value(A_VALUE));
        assertEquals(notWalked, at(HOT_HOLDS, notNarrowed));
        assertEquals(notWalked, at(HOT_HOLDS.denied(), notNarrowed));
    }

    private static CasesLeft casesOf(TypeSymbol... leaves) {
        return CasesLeft.ofEach(Arrays.stream(leaves)
                .map(leaf -> Refinement.of(new Case.SumCase(leaf, true))).toList());
    }

    private static AStatementAtARow.Answer at(Proposition stated,
                                              Map<TermPath, ObservationAtPoint> walked) {
        return AStatementAtARow.of(stated, "f", null).at(new AnObservationOfAForm() {

            @Override
            public WalkResult<ObservationAtPoint> at(TermPath path) {
                ObservationAtPoint there = walked.get(path);
                return there == null ? WalkResult.couldNotWalk() : WalkResult.reached(there);
            }

            @Override
            public WalkResult<List<ObservedValue>> everyValueAt(TermPath path) {
                throw new AssertionError("a case of one position is not read over a run");
            }
        });
    }
}
