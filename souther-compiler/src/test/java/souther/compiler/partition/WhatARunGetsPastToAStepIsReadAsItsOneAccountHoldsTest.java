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

    /** A reader of a construction, which reads in the names where the walk met each part, is
     *  handed the account whole, every part read in those names, or not at all: a part read in
     *  an application's names is neither met nor got past in other names. */
    @Test
    void aReaderOfAConstructionIsHandedTheAccountWholeOrNotAtAll() {
        Core onEveryRun = part(1);
        Core onSomeRuns = part(2);
        WhatARunWorksOutBeforeACount.BeforeAConstruction read = new BeforeAStep(List.of(
                new BeforeAStep.Part(onEveryRun, null, true),
                new BeforeAStep.Part(onSomeRuns, null, false))).asAConstructionReadsIt()
                .orElseThrow();
        assertEquals(List.of(onEveryRun, onSomeRuns), read.onSomeRun());
        assertEquals(List.of(onEveryRun), read.onEveryRun());
        assertEquals(Optional.empty(), new BeforeAStep(List.of(
                new BeforeAStep.Part(onEveryRun, null, true),
                new BeforeAStep.Part(part(3), names(), true))).asAConstructionReadsIt());
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
