package souther.compiler.program;

import souther.compiler.core.Core;
import souther.compiler.types.BindingId;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.Type;
import souther.compiler.types.ValueName;

import org.junit.jupiter.api.Test;

import java.util.List;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * A behavior says what it takes twice — as types on its signature, and as the bindings its body
 * reads them through — and a {@link CheckedBehavior} holding the two at different lengths is not
 * one that can be made.
 *
 * <p>Written against the model and not through a compile. What the assembler produces is held to
 * this by every module {@code AnOutputOutsideTheCompilerReadsACheckedProgramTest} compiles, and a
 * check only reached that way is a check that has never been asked its own question: it would go on
 * passing after the constructor stopped making it, because a correct assembler never offers it a
 * mismatch. Here the mismatch is offered.
 */
class ACheckedBehaviorHoldsItsTwoReadingsOfWhatItTakesTogetherTest {

    private static final Type INT = Type.INT;

    @Test
    void aBodyBindingFewerThanTheSignatureTakesIsRefused() {
        IllegalArgumentException refused = assertThrows(IllegalArgumentException.class,
                () -> behavior(List.of(INT, INT), body(binder("only"))));

        assertEquals("`demo.combine` takes 2 and its body binds 1", refused.getMessage());
    }

    @Test
    void andSoIsOneBindingMore() {
        assertThrows(IllegalArgumentException.class,
                () -> behavior(List.of(INT), body(binder("input"), binder("dependency"))),
                "a definition's trailing parameters are what it depends on, and are not inputs");
    }

    /**
     * And the invariant is one a behavior can satisfy.
     *
     * <p>A constructor that refused every argument would pass both tests above.
     */
    @Test
    void aBodyBindingWhatTheSignatureTakesIsMade() {
        CheckedBehavior made = behavior(List.of(INT, INT), body(binder("first"), binder("second")));

        assertEquals(List.of("first", "second"),
                ((CheckedImplementation.Body) made.implementation()).parameters().stream()
                        .map(Core.Binder::name).toList());
    }

    /** The states with no body of their own are not held to it, having no binders to be held by. */
    @Test
    void anImplementationWithNoBodyIsNotAskedWhichBindingsItsInputsArriveIn() {
        assertEquals(2, behavior(List.of(INT, INT), new CheckedImplementation.Injected())
                .signature().takes().size());
        assertEquals(2, behavior(List.of(INT, INT), new CheckedImplementation.Unwritten())
                .signature().takes().size());
    }

    private static CheckedBehavior behavior(List<Type> takes, CheckedImplementation implementation) {
        return new CheckedBehavior(new ValueName.Behavior("demo", "combine"),
                new CheckedSignature(takes, INT), implementation,
                souther.compiler.core.EnsuresEnforcement.NoContract.INSTANCE);
    }

    private static CheckedImplementation.Body body(Core.Binder... parameters) {
        return new CheckedImplementation.Body(List.of(parameters), new Core.Int(1, INT, null));
    }

    private static final BindingOwner OWNER = new BindingOwner.OfValue("demo", "combine");
    private static int next;

    private static Core.Binder binder(String name) {
        return new Core.Binder(name, new BindingId(OWNER, next++));
    }
}
