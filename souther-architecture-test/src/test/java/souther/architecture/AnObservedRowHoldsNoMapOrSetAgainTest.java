package souther.architecture;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * {@code Generator.ObservedRow} does not hold a {@code java.util.Map} or a {@code java.util.Set}
 * again.
 *
 * <p>Where a row's values sit is a {@link souther.compiler.carrier.Lookup}: every reader asks which
 * class the row is in at one position, and a {@code Map} that answered that would also offer a walk
 * over the positions, which a copy of it salts — differently on some runs than on others. Nothing
 * stops a future edit from giving the field a {@code Map} type again, and that edit would compile; so
 * this reads the field back and refuses it if it does ({@link MapOrSetFields}). About this carrier
 * alone and transitional in the way {@link AnInterpretationHoldsNoMapOrSetAgainTest} says.
 *
 * <p>A nested class is named as its class file names it, with a {@code $} between it and what it is
 * nested in.
 */
class AnObservedRowHoldsNoMapOrSetAgainTest {

    private static final String THE_CARRIER = "souther/compiler/partition/Generator$ObservedRow";

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    @Test
    void noFieldOfAnObservedRowIsAMapOrASet() {
        assertEquals(List.of(), MapOrSetFields.in(COMPILED.read(THE_CARRIER)),
                THE_CARRIER + " was moved off java.util.Map/Set — a field reading as one of those"
                        + " again is the same defect the move closed, and the walk a reader could"
                        + " take off it would be salted the same way");
    }
}
