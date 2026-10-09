package souther.compiler.semantics;

/**
 * How far an operation goes applying the closure it is handed to what a container holds, in the
 * order the container holds it.
 *
 * <p>A fact about the operation and not about any call of it: {@code List.any} answers once one
 * element holds, so an element after that one is handed to nothing, whatever the closure states.
 * Where the arguments are is read off the signature ({@link Combinator}); whether and how far the
 * closure is applied is read off the operation's body, or declared of a kernel and held to what the
 * kernel computes.
 */
public enum HowAClosureIsApplied {

    /** To every element, whatever any application answers. */
    TO_EVERY_ELEMENT,

    /** To each element in turn until one application answers true, and to none after it. */
    UNTIL_ONE_HOLDS,

    /** To each element in turn until one application answers false, and to none after it. */
    UNTIL_ONE_FAILS,

    /**
     * To one element at most — the one the call picks out by something else it was handed, if the
     * container holds it — and to no other. Which element, and whether any, is not said.
     */
    AT_MOST_ONE
}
