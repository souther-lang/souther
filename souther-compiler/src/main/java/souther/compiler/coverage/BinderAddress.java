package souther.compiler.coverage;

/**
 * Which binding a name in a body reads from, said as where the binder stands rather than as the
 * number the compiler minted for it.
 *
 * <p>A {@code BindingId} is a binder and its reads holding one value, which is what a pass needs and
 * is right for it. What it is made of is an owner and a count over that owner's bindings, and both
 * move: an expansion owns the copy it made and numbers copies as it makes them, so the same helper
 * spliced into the same body twice gives its bindings different owners, and a body edited above a
 * binder renumbers it. Neither changes what the body does.
 *
 * <p>So a reading that has to survive being taken twice reads a binding as a place. A binder that
 * stands inside the body is at a slot of a node, and the node is at an address; a name the body did
 * not bind is the behavior's own parameter, which the signature wrote and numbered.
 *
 * <p>There is no third arm on purpose. A read whose binding is neither is a body holding a name
 * nothing in sight binds, which is not something to give an address to.
 */
public sealed interface BinderAddress {

    /**
     * One of the behavior's parameters, which the signature binds and the body does not.
     *
     * @param index which parameter, in the order the signature writes them
     */
    record Parameter(String behavior, int index) implements BinderAddress {

        public Parameter {
            if (behavior == null) {
                throw new IllegalArgumentException("a parameter is somebody's parameter");
            }
            if (index < 0) {
                throw new IllegalArgumentException(
                        "a parameter stands somewhere among the signature's: " + index);
            }
        }

        @Override
        public String toString() {
            return behavior + "(" + index + ")";
        }
    }

    /** A binder standing at a slot of a node of the body. */
    record Local(NodeAddress owner, BinderSlot slot) implements BinderAddress {

        public Local {
            if (owner == null || slot == null) {
                throw new IllegalArgumentException("a binder stands at a slot of somewhere");
            }
        }

        @Override
        public String toString() {
            return owner + "." + slot;
        }
    }
}
