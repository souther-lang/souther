package souther.compiler.program;

/**
 * Whether a module publishes what it declares under a name, or keeps it.
 *
 * <p>Which is the question of whether a reader outside the module may name it: public elements are
 * the ones {@code exposing} lists, and a name reached across a module boundary must be one the
 * module exposes. A name the clause names is published and every other name the module declares is
 * kept, including where the module writes no clause at all — naming one of those from another
 * module is E1507.
 *
 * <p>Three other questions read the same clause and read it differently, and none of them is this
 * one. Whether Java may build a data from outside, and whether a generated class is public, are
 * both true of a module that writes no clause — a module that publishes nothing to Souther is
 * exactly the one written to be reached from Java. What a single-file run may reach is a third.
 * Each of those is that question's to answer, and this is the module's surface.
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
