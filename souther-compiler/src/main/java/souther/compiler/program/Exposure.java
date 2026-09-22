package souther.compiler.program;

/**
 * Whether a module publishes what it declares under a name, or keeps it.
 *
 * <p>A module's {@code exposing} clause says which of its names anything reading the module may
 * reach, and a module written without one publishes everything. Both are this answer: a reader is
 * told what the module publishes rather than handed a clause to read and a rule about what an
 * absent one means.
 *
 * <p>What an output does with it is the same decision in every carrier and is spelt differently in
 * each: the JVM makes a class public or leaves it package-private, and a native object either
 * gives a symbol to the linker or keeps it inside the object. An output deciding for itself which
 * names it publishes would be publishing a surface the module never stated.
 *
 * <p>An answer and not a flag, because the two are not each other's absence: a name is published
 * because the module says so, and kept because the module says so, and a module with no clause
 * says the first of everything.
 */
public enum Exposure {

    /** The module publishes it. Anything that may read the module may reach this. */
    EXPOSED,

    /** The module keeps it. Only the module itself reaches it. */
    KEPT
}
