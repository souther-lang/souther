package souther.compiler.semantics;

/**
 * How far an operation goes applying the closure it is handed to what a container holds, in the
 * order the container holds it.
 *
 * <p>A fact about the operation and not about any call of it: {@code List.any} answers once one
 * element holds, so an element after that one is handed to nothing, whatever the closure states.
 * What the closure is handed is read off the signature ({@link Combinator}); where the operation
 * stops is not in a signature, so it is declared beside it and held to what the library computes.
 */
public enum HowAClosureIsApplied {

    /** To every element, whatever any application answers. */
    TO_EVERY_ELEMENT,

    /** To each element in turn until one application answers true, and to none after it. */
    UNTIL_ONE_HOLDS,

    /** To each element in turn until one application answers false, and to none after it. */
    UNTIL_ONE_FAILS
}
