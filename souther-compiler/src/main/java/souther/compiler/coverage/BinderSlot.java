package souther.compiler.coverage;

/**
 * Which of a node's binders one is.
 *
 * <p>Beside {@link CoreStructure.Edge} rather than among it. An edge leads to a child, and every
 * child is an expression the walk goes on into; a binder is neither — it is a name the node opens
 * for what stands under it, and there is nothing below it to walk. Held as one vocabulary they
 * would be a step down that goes nowhere, which a path is not.
 *
 * <p>One arm per node kind that opens a name, and no more: a node kind that starts binding arrives
 * here as a case the walk cannot answer rather than as a binder nothing can address.
 */
public sealed interface BinderSlot {

    /** The name a {@code let} opens for its body. */
    record LetBinder() implements BinderSlot {

        @Override
        public String toString() {
            return "let";
        }
    }

    /** One of the names a function value takes. */
    record BlockParam(int index) implements BinderSlot {

        public BlockParam {
            if (index < 0) {
                throw new IllegalArgumentException("a parameter stands somewhere: " + index);
            }
        }

        @Override
        public String toString() {
            return "param(" + index + ")";
        }
    }

    /** The name a {@code match} case opens for what it matched. */
    record CaseBinder(int index) implements BinderSlot {

        public CaseBinder {
            if (index < 0) {
                throw new IllegalArgumentException("a case stands somewhere: " + index);
            }
        }

        @Override
        public String toString() {
            return "case(" + index + ")";
        }
    }

    /** The name an attempted construction opens for what it built. */
    record ConstructedBinder() implements BinderSlot {

        @Override
        public String toString() {
            return "built";
        }
    }
}
