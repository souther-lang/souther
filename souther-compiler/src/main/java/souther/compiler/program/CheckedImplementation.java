package souther.compiler.program;

import souther.compiler.core.Composition;
import souther.compiler.core.Core;

import java.util.List;

/**
 * Where a behavior's implementation comes from, in the four states a checked module has them in.
 *
 * <p>Four and not a body that may be absent. A composition is an implementation (spec
 * §sequential-composition) and has no body: a reader given {@code Optional<Core>} would find nothing
 * there and have to decide what nothing meant, and the two things it can mean — composed, and not
 * written yet — are different programs. Nothing here has to be recovered from a second fact.
 */
public sealed interface CheckedImplementation {

    /**
     * Written here, as a {@code let} of the behavior's name: the checker's Core for it, and the
     * bindings its inputs arrive in.
     *
     * <p>{@code parameters} holds the binders of the behavior's declared inputs, in the order
     * {@link CheckedSignature#takes()} is in — so the {@code i}th input is
     * {@code parameters().get(i)} and {@code signature().takes().get(i)}, and a read of that
     * binding in {@code body} is a read of that input. A behavior's injected dependencies are not
     * among them: they are not passed at a call, and a body reaches one by its name rather than by
     * reading a binding.
     *
     * <p>The binders and not the types. A type here would be a second reading of what
     * {@link CheckedSignature} already answers, and the two would agree until either moved.
     * {@link CheckedBehavior} is where they are held to the same length, which is what makes
     * reading them as one parameter safe.
     *
     * <p>Here and not on {@link CheckedBehavior}, because a binder exists exactly where a body
     * does. An injected behavior takes inputs and has no body to bind them in, an unwritten one has
     * none either, and a composition applies its first stage to what it was given. Answering this
     * for any of them would be answering a question that has no answer.
     */
    record Body(List<Core.Binder> parameters, Core body) implements CheckedImplementation {

        public Body {
            // Copied and not held: a caller that kept its list could change what the snapshot says
            // a body's inputs are. `List.copyOf` refuses a null among them, and a parameter's
            // binder is never the absent one a `match` arm binding nothing has.
            parameters = List.copyOf(parameters);
            if (body == null) {
                throw new IllegalArgumentException("an implemented behavior has a body");
            }
        }
    }

    /** Written here as {@code >->}: the stages, and what each is offered (spec §type-routing). */
    record Composed(Composition composition) implements CheckedImplementation {

        public Composed {
            if (composition == null) {
                throw new IllegalArgumentException("a composed behavior has stages");
            }
        }
    }

    /** Supplied from outside Souther (spec §injected-behavior). What it does is not in the program;
     *  the declaration and its signature are. */
    record Injected() implements CheckedImplementation {}

    /** Souther's to write, and not written (spec §unwritten-behavior). Nothing that would need the
     *  body it has not got is emitted. */
    record Unwritten() implements CheckedImplementation {}
}
