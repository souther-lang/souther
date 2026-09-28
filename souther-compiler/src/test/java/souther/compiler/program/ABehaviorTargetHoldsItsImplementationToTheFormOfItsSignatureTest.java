package souther.compiler.program;

import souther.compiler.core.Composition;
import souther.compiler.core.Core;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.LeafScalar;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertDoesNotThrow;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A declaration names every parameter and a composition names none, and each implementation is
 * written against one of them: a {@link BehaviorTarget} pairing an implementation with the other
 * form is not one that can be made.
 *
 * <p>Written against the model and not through a compile, for the reason
 * {@link ABehaviorTargetHoldsItsTwoReadingsOfWhatItTakesTogetherTest} is: a correct assembler never
 * offers the constructor a mismatch, so only here is the refusal asked for.
 *
 * <p>Both forms are made with {@link CheckedImplementation.ImplementedElsewhere}, which is either.
 * That the signature carries which one is what keeps a published composition from being read as a
 * declaration.
 */
class ABehaviorTargetHoldsItsImplementationToTheFormOfItsSignatureTest {

    private static final CheckedBoundaryInput INT_IN =
            new CheckedBoundaryInput.Scalar(LeafScalar.INT);
    private static final CheckedBoundaryOutput INT_OUT =
            new CheckedBoundaryOutput.Scalar(LeafScalar.INT);

    private static final CheckedSignature DECLARED = CheckedSignature.declared(
            List.of(new CheckedSignature.Parameter("x", INT_IN)), INT_OUT);
    private static final CheckedSignature COMPOSED =
            CheckedSignature.composed(List.of(INT_IN), INT_OUT);

    @Test
    void aDeclarationIsWrittenAsABodyInjectedOrUnwritten() {
        assertDoesNotThrow(() -> target(DECLARED, body()));
        assertDoesNotThrow(() -> target(DECLARED, new CheckedImplementation.Injected()));
        assertDoesNotThrow(() -> target(DECLARED, new CheckedImplementation.Unwritten()));
    }

    @Test
    void aDeclarationIsNotWrittenAsAComposition() {
        assertThrows(IllegalArgumentException.class, () -> target(DECLARED, composed()));
    }

    @Test
    void aCompositionIsWrittenAsAComposition() {
        assertDoesNotThrow(() -> target(COMPOSED, composed()));
    }

    @Test
    void aCompositionIsNotWrittenAsABodyInjectedOrUnwritten() {
        assertThrows(IllegalArgumentException.class, () -> target(COMPOSED, body()));
        assertThrows(IllegalArgumentException.class,
                () -> target(COMPOSED, new CheckedImplementation.Injected()));
        assertThrows(IllegalArgumentException.class,
                () -> target(COMPOSED, new CheckedImplementation.Unwritten()));
    }

    @Test
    void anImplementationAnotherCompileEmittedIsEitherForm() {
        assertDoesNotThrow(() -> target(DECLARED, new CheckedImplementation.ImplementedElsewhere()));
        assertDoesNotThrow(() -> target(COMPOSED, new CheckedImplementation.ImplementedElsewhere()));
    }

    /** Requiring nothing to construct, which every implementation may: the form of the signature is
     *  the only thing asked of it here. */
    private static BehaviorTarget target(CheckedSignature signature,
                                         CheckedImplementation implementation) {
        return new BehaviorTarget(signature, implementation, List.of());
    }

    private static CheckedImplementation.Body body() {
        BindingOwner owner = new BindingOwner.OfValue("demo", "f");
        return new CheckedImplementation.Body(
                List.of(new Core.Binder("x", new BindingId(owner, 0))),
                new Core.Int(1, Type.INT, null));
    }

    private static CheckedImplementation.Composed composed() {
        return new CheckedImplementation.Composed(new Composition(
                List.of(new Composition.Stage(new ValueName.Behavior("demo", "g"), Type.INT,
                        new Composition.Routing.Always())),
                Type.INT));
    }
}
