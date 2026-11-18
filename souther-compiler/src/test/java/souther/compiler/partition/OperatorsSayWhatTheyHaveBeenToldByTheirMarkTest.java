package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.InputReads;
import souther.compiler.partition.ReadingState.Restore;
import souther.compiler.partition.ReadingState.Scoped;
import souther.compiler.types.Type;

import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotEquals;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What the operators of a reading have been told ({@link Operators#mark}) moves with everything
 * they are told, and stands for them wherever a reading is compared on them.
 *
 * <p>A reading kept under one set of operators is taken again under the same set only while
 * they have been told nothing more, and only where what is set for the extent being read — the
 * application, what the names of a walk's step hold — is what it was: the very object is not
 * enough, since it is changed in place.
 */
class OperatorsSayWhatTheyHaveBeenToldByTheirMarkTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static Core number(long value) {
        return new Core.Int(value, Type.INT, POS);
    }

    private static InputReads.Applications.Made anApplication() {
        return new InputReads.Applications.Made(InputReads.ofWhatIsDeclared(Map.of(), null),
                List.of(), Optional.empty());
    }

    @Test
    void anOperatorToldOnceMovesTheMarkAndToldAgainDoesNot() {
        Operators operators = new Operators();
        Core sum = number(1);
        Object before = operators.mark();

        operators.tell(sum, new Pullback.Answers.Anywhere());
        Object told = operators.mark();
        assertNotEquals(before, told);

        operators.tell(sum, new Pullback.Answers.Anywhere());
        assertEquals(told, operators.mark(), "telling it again says nothing more");
    }

    @Test
    void whatIsSetForAnExtentIsInTheMarkAndPuttingItBackPutsTheMarkBack() {
        Operators operators = new Operators();
        Object before = operators.mark();

        try (Restore _ = operators.onTheApplication(anApplication())) {
            assertNotEquals(before, operators.mark());
        }
        assertEquals(before, operators.mark());

        try (Restore _ = operators.withTheStepsNames(new Pullback.WhatTheStepsNamesHold(
                null, null, Map.of()))) {
            assertNotEquals(before, operators.mark());
        }
        assertEquals(before, operators.mark());
    }

    @Test
    void whatTheyLeaveUnsaidMovesTheMark() {
        Operators operators = new Operators();
        Object before = operators.mark();

        operators.leaveUnsaidOverUnreadOperands();
        Object unsaid = operators.mark();
        assertNotEquals(before, unsaid);

        operators.leaveUnsaidOverUnreadOperands();
        assertEquals(unsaid, operators.mark(), "it was unsaid already");

        operators.beginGroup();
        assertNotEquals(unsaid, operators.mark());
    }

    /**
     * The operators of the applications after the first are their own: what they are told is
     * not told to the operators they were made from, which neither change nor take the operator
     * as told.
     */
    @Test
    void theOperatorsOfTheApplicationsAfterTheFirstShareNothingWithThoseTheyWereMadeFrom() {
        Operators first = new Operators();
        InputReads.Applications.Made application = anApplication();
        Core sum = number(1);
        try (Restore _ = first.onTheApplication(anApplication())) {
            first.tell(sum, new Pullback.Answers.Anywhere());
        }
        Operators rest = first.ofTheApplicationsAfterTheFirst();
        Object before = first.mark();

        try (Restore _ = rest.onTheApplication(application)) {
            rest.tell(sum, new Pullback.Answers.Anywhere());
        }
        assertEquals(before, first.mark());
        assertEquals(1, first.toldSoFar());

        try (Restore _ = first.onTheApplication(application)) {
            first.tell(sum, new Pullback.Answers.Anywhere());
        }
        assertEquals(2, first.toldSoFar(), "told on that application here for the first time");
    }

    @Test
    void aReadingIsComparedOnTheOperatorsByWhatTheyHaveBeenToldAndNotByWhichTheyAre() {
        ReadingState state = new ReadingState();
        Scoped<Operators> operated = state.guardedByItsMark();
        Operators operators = new Operators();
        try (Restore _ = operated.set(operators)) {
            ReadingState.Inputs then = state.inputs();
            List<Object[]> guards = state.guards();
            assertTrue(state.sameInputs(then, state.inputs(), false, 0));

            operators.tell(number(1), new Pullback.Answers.Anywhere());

            assertFalse(state.sameInputs(then, state.inputs(), false, 0),
                    "the same operators, told more since");
            assertFalse(state.sameGuards(guards, state.guards()));
        }
    }
}
