package souther.architecture;

import org.junit.jupiter.api.Test;

/**
 * {@code BehaviorInputs.Occurrence} does not hold a {@code java.util.Map} or a {@code java.util.Set}
 * again.
 *
 * <p>The elements it was reached through are {@link souther.compiler.observe.ElementsTaken}, which
 * keeps them outermost first: the readings of a row over its steps are built and cut at a bound from
 * that order, and a copy that salted it would decide which readings survive. Nothing stops a future
 * edit from giving the field a map again, and that edit would compile; so it is read back
 * ({@link MapOrSetFields}). About this carrier alone, and transitional in the way
 * {@link AnInterpretationHoldsNoMapOrSetAgainTest} says.
 */
class AnOccurrenceHoldsNoMapOrSetAgainTest {

    @Test
    void noFieldOfAnOccurrenceIsAMapOrASet() {
        MapOrSetFields.assertHoldsNone(CompiledOutputs.ofWhatThisRepositoryPublishes(),
                "souther/compiler/partition/BehaviorInputs$Occurrence");
    }
}
