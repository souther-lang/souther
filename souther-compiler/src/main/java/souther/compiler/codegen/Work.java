package souther.compiler.codegen;

/**
 * Whether a call from generated code into the runtime does work that grows with a value it is
 * handed, which is what decides whether an evaluated class hands it a checkpoint.
 *
 * <p>Every runtime call this backend emits states one or the other, as a component of the row or
 * the call that emits it, so a call cannot be written without saying which it is. What is asked is
 * not whether a value is bounded — every value is, by what a value of its type may hold — but
 * whether the call's work turns on how large the value is.
 */
enum Work {

    /**
     * The work is bounded by a constant, whatever the values: an {@code Int}'s arithmetic, a date's
     * field, a step of a trie whose depth is a hash's bits, an operation over a tuple whose arity the
     * source wrote.
     */
    FIXED,

    /**
     * The work grows with a value: a text's characters, a collection's elements, a number's digits.
     * An evaluated class calls the runtime's entry that takes the evaluation's checkpoint as its
     * last argument; a class that ships calls the one that takes none.
     */
    CHECKPOINTED
}
