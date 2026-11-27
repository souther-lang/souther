package souther.compiler.program;

import souther.compiler.core.EnsuresEnforcement;
import souther.compiler.types.LeafScalar;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.ArrayList;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Souther does not construct an injected behavior, so a {@link BehaviorTarget} saying one requires
 * something to construct is not one that can be made — and that is the only implementation held to
 * what its construction requires.
 *
 * <p>Written against the model and not through a compile, for the reason
 * {@link ABehaviorTargetHoldsItsTwoReadingsOfWhatItTakesTogetherTest} is: a correct assembler never
 * offers the constructor an injected behavior with requirements, so only here is the refusal asked
 * for.
 */
class ABehaviorTargetHoldsItsConstructionRequirementsToItsImplementationTest {

    private static final CheckedSignature DECLARED = CheckedSignature.declared(
            List.of(new CheckedSignature.Parameter("x",
                    new CheckedBoundaryInput.Scalar(LeafScalar.INT))),
            new CheckedBoundaryOutput.Scalar(LeafScalar.INT));

    private static final ValueName.Behavior FIRST = new ValueName.Behavior("lib", "first");
    private static final ValueName.Behavior SECOND = new ValueName.Behavior("lib", "second");

    /** What a target of a behavior declaring nothing of its answer is checked by. */
    private static final EnsuresEnforcement NOTHING = EnsuresEnforcement.NoContract.INSTANCE;

    @Test
    void anInjectedBehaviorSaidToRequireSomethingIsRefused() {
        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> new BehaviorTarget(DECLARED, new CheckedImplementation.Injected(),
                        List.of(FIRST), NOTHING));

        assertEquals("an injected behavior is not constructed by Souther, and is said to require"
                + " [lib.first]", refused.getMessage());
    }

    /** And an injected behavior requiring nothing is made: a constructor refusing every injected
     *  behavior would pass the test above. */
    @Test
    void anInjectedBehaviorRequiringNothingIsMade() {
        assertEquals(List.of(), new BehaviorTarget(DECLARED, new CheckedImplementation.Injected(),
                List.of(), NOTHING).requirements());
    }

    /** An unwritten behavior may declare what it depends on before anyone writes it: what it
     *  requires is not where its implementation comes from. */
    @Test
    void anUnwrittenBehaviorMayRequireWhatItDeclaresItDependsOn() {
        assertEquals(List.of(FIRST, SECOND),
                new BehaviorTarget(DECLARED, new CheckedImplementation.Unwritten(),
                        List.of(FIRST, SECOND), NOTHING).requirements());
    }

    /** And so may one another compile emitted, in the order it was published in. */
    @Test
    void aBehaviorImplementedElsewhereKeepsTheOrderItWasHanded() {
        assertEquals(List.of(SECOND, FIRST),
                new BehaviorTarget(DECLARED, new CheckedImplementation.ImplementedElsewhere(),
                        List.of(SECOND, FIRST), NOTHING).requirements());
    }

    /** What it was handed is copied, so a list changed afterwards does not change what the target
     *  says. */
    @Test
    void theRequirementsAreHeldAsTheyWereHanded() {
        List<ValueName.Behavior> handed = new ArrayList<>(List.of(FIRST));
        BehaviorTarget made = new BehaviorTarget(DECLARED, new CheckedImplementation.Unwritten(),
                handed, NOTHING);
        handed.add(SECOND);

        assertEquals(List.of(FIRST), made.requirements());
    }
}
