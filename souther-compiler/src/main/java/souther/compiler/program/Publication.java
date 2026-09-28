package souther.compiler.program;

/**
 * Whether a module publishes what it declares under a name, or keeps it.
 *
 * <p>Which is the question of whether a reader outside the module may name it, and a name reached
 * across a module boundary must be one the module publishes — naming one it keeps from another
 * module is E1507. A module that writes no {@code exposing} clause publishes every declaration it
 * makes; one that writes a clause publishes what the clause names and keeps the rest, so
 * {@code exposing ()} keeps everything (spec §a-module-publishes-what-it-declares).
 *
 * <p>Worked out once, where the module's declarations are read, and read from there by every
 * question that turns on it: whether Java may build a data from outside, whether a declaration's
 * generated class is public, and what a single-file run may reach.
 *
 * <p><b>Not what an artifact makes visible.</b> The two are different questions and the answers
 * come apart in both directions. A published helper runs in the module that reads it, so the JVM
 * puts it on a class that module keeps — published, and not visible. The base class of an injected
 * behavior is public whatever the clause says — kept, and visible. What a carrier makes visible is
 * worked out from this together with what the artifact is for, and a carrier that read this as its
 * answer would be publishing a surface the module never stated or hiding one it did.
 *
 * <p>An answer and not a flag, because a name is published because the module says so and kept
 * because the module says so, and neither is the other's absence.
 */
public enum Publication {

    /** The module publishes it. Anything that may read the module may name this. */
    PUBLISHED,

    /** The module keeps it. Only the module itself names it. */
    KEPT
}
