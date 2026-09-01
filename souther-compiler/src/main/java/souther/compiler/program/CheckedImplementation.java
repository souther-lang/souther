package souther.compiler.program;

import souther.compiler.core.Composition;
import souther.compiler.core.Core;

import java.util.List;

/**
 * Where a behavior's implementation comes from, as this checked program can state it.
 *
 * <p>Answered for every behavior this compile read the declaration of, which is wider than the
 * modules it checked: a body may call a behavior a module on the path declares, and what an output
 * emitting that call needs is this. So the states are not the ones a checked module's behaviors are
 * in — {@link ImplementedElsewhere} is none of them — but the ones a snapshot can say a behavior's
 * implementation is in.
 *
 * <p>Each state, and not a body that may be absent. A composition is an implementation (spec
 * §sequential-composition) and has no body; so is an implementation another compile emitted. A
 * reader given {@code Optional<Core>} would find nothing there and have to decide what nothing
 * meant, and the three things it can mean are different programs. Nothing here has to be recovered
 * from a second fact.
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

    /**
     * Implemented, and the implementation is not this snapshot's: the module that declares it was
     * read off the path, and the build that published it emitted the implementation already.
     *
     * <p>What a call to one reaches is written, so a caller has a callee rather than a crossing to
     * something supplied from outside. What is not here is the {@link Core} or the
     * {@link Composition} it is written as — that belongs to the compile that checked it, and a
     * second one emitted under the same name would be two definitions of one behavior.
     *
     * <p>Says nothing about how a call to it is reached on some machine. Whether an output links
     * the implementation in, calls across a module boundary, or imports it is that output's answer,
     * for the reason a class name and a Wasm block are not decided here.
     */
    record ImplementedElsewhere() implements CheckedImplementation {}
}
