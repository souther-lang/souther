package souther.architecture;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * {@code DecisionSubjects} does not hold a {@code java.util.Map} or a {@code java.util.Set} again.
 *
 * <p>What it holds of the behaviors this one depends on is a {@link
 * souther.compiler.carrier.Membership}, which answers whether a behavior is one of them and offers
 * no {@code iterator}, {@code stream} or {@code forEach} to take an order off. A {@code Set} offers
 * all three, and a {@code Set} built by copying one salts the order those hand back — differently on
 * some runs than on others — so every reader of it has to ask whether a behavior is in, which is all
 * a {@code Membership} lets a reader do.
 *
 * <p>Nothing stops a future edit from giving that field a {@code Set} type again, and that edit
 * would compile; so this reads the field back and refuses it if it does ({@link MapOrSetFields}).
 * About this carrier alone and transitional in the way {@link
 * AnInterpretationHoldsNoMapOrSetAgainTest} says.
 */
class ADecisionSubjectsHoldsNoMapOrSetAgainTest {

    private static final String THE_CARRIER = "souther/compiler/partition/DecisionSubjects";

    private static final CompiledOutputs COMPILED = CompiledOutputs.ofWhatThisRepositoryPublishes();

    @Test
    void noFieldOfDecisionSubjectsIsAMapOrASet() {
        assertEquals(List.of(), MapOrSetFields.in(COMPILED.read(THE_CARRIER)),
                THE_CARRIER + " was moved off java.util.Map/Set — a field reading as one of those"
                        + " again is the same defect the move closed, and the walk a reader could"
                        + " take off it would be salted the same way");
    }
}
