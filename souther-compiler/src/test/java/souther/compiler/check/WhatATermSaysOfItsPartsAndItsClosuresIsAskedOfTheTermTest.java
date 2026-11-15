package souther.compiler.check;

import org.junit.jupiter.api.Test;
import souther.compiler.types.ValueName;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNotSame;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertSame;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A closure answers as one parameter does only where its payload says it takes one: its body is
 * its one part however many parameters it has. And a sum of sizes is the sum of what its measures
 * count, so the same two terms counted another way are another sum.
 */
class WhatATermSaysOfItsPartsAndItsClosuresIsAskedOfTheTermTest {

    private static final ValueName LENGTH = new ValueName.Helper("List", "length");
    private static final ValueName SIZE = new ValueName.Helper("Set", "size");

    private final Term.Interner interned = new Term.Interner();

    @Test
    void aClosureOfOneParameterAnswersItsBody() {
        Term body = interned.bound(0, 0);
        assertSame(body, interned.closure(1, body).answerOfAClosureOfOneParameter());
    }

    @Test
    void aClosureOfTwoParametersHasOneBodyAndIsNoClosureOfOneParameter() {
        Term body = interned.bound(0, 0);
        assertEquals(1, interned.closure(2, body).parts().size());
        assertNull(interned.closure(2, body).answerOfAClosureOfOneParameter());
    }

    @Test
    void aTermOfOnePartThatIsNoClosureAnswersNothing() {
        Term one = interned.bound(0, 0);
        assertEquals(1, interned.called(LENGTH, List.of(one)).parts().size());
        assertNull(interned.called(LENGTH, List.of(one))
                .answerOfAClosureOfOneParameter());
    }

    @Test
    void aTermHoldsItselfAndWhatItIsBuiltOverAndNothingElse() {
        Term inner = interned.bound(0, 0);
        Term other = interned.bound(0, 1);
        Term outer = interned.called(LENGTH, List.of(interned.called(SIZE, List.of(inner))));
        assertTrue(outer.holds(outer));
        assertTrue(outer.holds(inner));
        assertFalse(outer.holds(other));
    }

    @Test
    void theSameTermsCountedByAnotherMeasureAreAnotherSum() {
        Term container = interned.bound(0, 0);
        Term byLength = interned.sumOfSizes(container, null, new Term.CountedBy(LENGTH, LENGTH));
        Term bySize = interned.sumOfSizes(container, null, new Term.CountedBy(SIZE, LENGTH));
        Term eachBySize = interned.sumOfSizes(container, null, new Term.CountedBy(LENGTH, SIZE));
        Term uncounted = interned.sumOfSizes(container, null, new Term.CountedBy(LENGTH, null));
        assertSame(byLength,
                interned.sumOfSizes(container, null, new Term.CountedBy(LENGTH, LENGTH)));
        assertNotSame(byLength, bySize);
        assertNotSame(byLength, eachBySize);
        assertNotSame(byLength, uncounted);
    }
}
