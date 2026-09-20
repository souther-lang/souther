package souther.architecture;

import org.junit.jupiter.api.Test;

/**
 * {@code ReachingCuts} does not hold a {@code java.util.Map} or a {@code java.util.Set} again.
 *
 * <p>What the walk collected at each comparison is a {@link souther.compiler.carrier.Lookup}:
 * production asks it by comparison and nothing else, and a map that answered that would also offer a
 * walk over the comparisons, which a copy salts. Nothing stops a future edit from giving the field a
 * map again, and that edit would compile; so it is read back ({@link MapOrSetFields}). About this
 * carrier alone, and transitional in the way {@link AnInterpretationHoldsNoMapOrSetAgainTest} says.
 */
class AReachingCutsHoldsNoMapOrSetAgainTest {

    @Test
    void noFieldOfReachingCutsIsAMapOrASet() {
        MapOrSetFields.assertHoldsNone(CompiledOutputs.ofWhatThisRepositoryPublishes(),
                "souther/compiler/partition/ReachingCuts");
    }
}
