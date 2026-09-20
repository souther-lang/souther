package souther.architecture;

import org.junit.jupiter.api.Test;

/**
 * {@code Generator.Baseline} does not hold a {@code java.util.Map} or a {@code java.util.Set} again.
 *
 * <p>The values a module states, by the parameter each is of, are a
 * {@link souther.compiler.carrier.Lookup}: readers ask which value stands at a parameter and nothing
 * else, and whether there are any is the origin's to say and not a lookup's. Nothing stops a future
 * edit from giving the field a map again, and that edit would compile; so it is read back
 * ({@link MapOrSetFields}). About this carrier alone, and transitional in the way
 * {@link AnInterpretationHoldsNoMapOrSetAgainTest} says.
 */
class ABaselineHoldsNoMapOrSetAgainTest {

    @Test
    void noFieldOfABaselineIsAMapOrASet() {
        MapOrSetFields.assertHoldsNone(CompiledOutputs.ofWhatThisRepositoryPublishes(),
                "souther/compiler/partition/Generator$Baseline");
    }
}
