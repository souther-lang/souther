package souther.compiler.types;

import java.util.Objects;

/**
 * One application a call of the model makes of the closure it is handed: the call, as the construct
 * of the model it is, and the element the application is handed, by its place among the elements
 * the call's container is written out as, counting from nought and counting those a filter drops
 * too.
 *
 * <p>What the two readings of a body both tell an application by. In the reading where the
 * language's operations are expanded the call is gone, the closure is applied by a walk inside a
 * copy of the operation's body, and its parameters are bindings of that copy; what is left of the
 * call is the construct of the model the copy was made at ({@link ModelOccurrence}). A helper
 * called twice is two constructs of the model, so the applications each copy makes are its own.
 *
 * <p>By the place the element is written at and not by how many applications came before it. Which
 * elements a run is handed is decided by each reader of the container, and two readers deciding
 * apart would count one application two ways; where an element is written is the walk of the
 * container's to say, and is the same for both. Two elements written alike are two places.
 *
 * <p>An application by the element it is handed, and not a count of them. An operation that applies
 * its closure to every element may hand one element over twice, and both are named by this; what
 * the closure states on the element is what it states on either, so a reader may take that and
 * may not read off this how many applications a run makes.
 *
 * <p>An application of the call, and not of one closure: a call handed two closures it applies to
 * each element makes an application of both on each, and this names the two. What is read on
 * one is read at the sites of its own body, so what is filed under this is the sites of both, each
 * stating what its closure states there.
 *
 * @param call    the call of the model that makes it
 * @param written the place, among the elements of the call's container as written out, of the
 *                element it is handed
 */
public record AnApplicationOfACall(ModelOccurrence call, int written) {

    public AnApplicationOfACall {
        Objects.requireNonNull(call, "an application is made by some call of the model");
        if (written < 0) {
            throw new IllegalArgumentException("elements are counted from nought: " + written);
        }
    }
}
