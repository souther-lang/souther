package souther.architecture;

import org.junit.jupiter.api.Test;

/**
 * {@code Classification.At} does not hold a {@code java.util.Map} or a {@code java.util.Set} again.
 *
 * <p>The elements a class was reached through are {@link souther.compiler.observe.ElementsTaken},
 * the same value the row's occurrences hold. Nothing stops a future edit from giving the field a map
 * again, and that edit would compile; so it is read back ({@link MapOrSetFields}). About this
 * carrier alone, and transitional in the way {@link AnInterpretationHoldsNoMapOrSetAgainTest} says.
 */
class AClassificationAtHoldsNoMapOrSetAgainTest {

    @Test
    void noFieldOfAClassificationAtIsAMapOrASet() {
        MapOrSetFields.assertHoldsNone(CompiledOutputs.ofWhatThisRepositoryPublishes(),
                "souther/compiler/observe/Classification$At");
    }
}
