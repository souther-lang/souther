package souther.compiler.types;

import java.util.Objects;

/**
 * One application a call of the model makes of the closure it is handed: the call, as the construct
 * of the model it is, and which of its applications this is, counting from nought in the order a
 * run makes them.
 *
 * <p>What the two readings of a body both tell an application by. In the reading where the
 * language's operations are expanded the call is gone, the closure is applied by a walk inside a
 * copy of the operation's body, and its parameters are bindings of that copy; what is left of the
 * call is the construct of the model the copy was made at ({@link ModelOccurrence}). A helper
 * called twice is two constructs of the model, so the applications each copy makes are its own.
 *
 * @param call    the call of the model that makes it
 * @param ordinal which of the call's applications it is
 */
public record AnApplicationOfACall(ModelOccurrence call, int ordinal) {

    public AnApplicationOfACall {
        Objects.requireNonNull(call, "an application is made by some call of the model");
        if (ordinal < 0) {
            throw new IllegalArgumentException("applications are counted from nought: " + ordinal);
        }
    }
}
