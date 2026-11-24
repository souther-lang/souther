package souther.compiler.partition;

import org.junit.jupiter.api.Test;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.inputs.DeclaredInput;
import souther.compiler.inputs.InputReads;
import souther.compiler.types.Type;

import java.util.List;
import java.util.Map;
import java.util.Optional;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * What a run works out before a step is one account ({@link BeforeAStep}), and what a reader
 * takes as met of it is never more than the account holds: a part read in names of its own is
 * not met by a reader that reads in others, and what one application works out comes after what
 * a run works out going into the tree it stands in, or is not read at all.
 */
class WhatARunGetsPastToAStepIsReadAsItsOneAccountHoldsTest {

    private static final SourcePos POS = new SourcePos(1, 1);

    private static Core part(long value) {
        return new Core.Int(value, Type.INT, POS);
    }

    /** Some names a part is read in, which are not the ones where the walk met it. */
    private static InputReads names() {
        return InputReads.ofWhatIsDeclared(Map.of(), DeclaredInput.NONE);
    }

    /** A part worked out on every run is met by a reader of a construction only where it is
     *  read in the names that reader reads in; one read in an application's names is only got
     *  past. */
    @Test
    void aPartReadInNamesOfItsOwnIsNotMetByAReaderOfAConstruction() {
        Core inTheWalkersNames = part(1);
        Core inAnApplicationsNames = part(2);
        Core onSomeRuns = part(3);
        WhatARunWorksOutBeforeACount.BeforeAConstruction read = new BeforeAStep(List.of(
                new BeforeAStep.Part(inTheWalkersNames, null, true),
                new BeforeAStep.Part(inAnApplicationsNames, names(), true),
                new BeforeAStep.Part(onSomeRuns, null, false))).asAConstructionReadsIt();
        assertEquals(List.of(inTheWalkersNames, inAnApplicationsNames, onSomeRuns),
                read.onSomeRun());
        assertEquals(List.of(inTheWalkersNames), read.onEveryRun());
    }

    /** What one application works out comes after what a run works out going into the tree,
     *  and where that is not read, neither is what comes before the step. */
    @Test
    void anApplicationComesAfterWhatARunWorksOutGoingInAndIsNotReadWithoutIt() {
        Core goingIn = part(1);
        Core inside = part(2);
        Optional<BeforeAStep> read = BeforeAStep.onAnApplication(Optional.of(
                        new WhatARunWorksOutBeforeACount.BeforeAConstruction(List.of(goingIn),
                                List.of(goingIn))),
                List.of(new BeforeAStep.Part(inside, names(), true)));
        assertTrue(read.isPresent());
        assertSame(goingIn, read.get().parts().get(0).node());
        assertTrue(read.get().parts().get(0).every());
        assertSame(inside, read.get().parts().get(1).node());
        assertEquals(Optional.empty(), BeforeAStep.onAnApplication(Optional.empty(),
                List.of(new BeforeAStep.Part(inside, names(), true))));
    }
}
