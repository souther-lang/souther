package souther.compiler.program;

import souther.compiler.core.Composition;
import souther.compiler.core.Core;

/**
 * Where a behavior's implementation comes from, in the four states a checked module has them in.
 *
 * <p>Four and not a body that may be absent. A composition is an implementation (spec
 * §sequential-composition) and has no body: a reader given {@code Optional<Core>} would find nothing
 * there and have to decide what nothing meant, and the two things it can mean — composed, and not
 * written yet — are different programs. Nothing here has to be recovered from a second fact.
 */
public sealed interface CheckedImplementation {

    /** Written here, as a {@code let} of the behavior's name: the checker's Core for it. */
    record Body(Core body) implements CheckedImplementation {

        public Body {
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
