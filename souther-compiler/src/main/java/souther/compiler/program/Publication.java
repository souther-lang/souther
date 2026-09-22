package souther.compiler.program;

/**
 * Whether a module publishes what it declares under a name, or keeps it.
 *
 * <p>The module's {@code exposing} clause decides it and nothing else does: a name the clause names
 * is published, and every other name the module declares is kept — including where the module
 * writes no clause at all, which publishes nothing (E1507 is what an importer is told).
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
