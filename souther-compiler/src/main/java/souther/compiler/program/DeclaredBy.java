package souther.compiler.program;

/**
 * Who declared a data: a module this compile checked, the language itself, or a module this compile
 * read off the path.
 *
 * <p>Provenance and nothing else. What a value of it is made of is answered the same way for all
 * three — that is what {@link Declared} being one thing says — and this is the question an output
 * asks when it is deciding what to emit rather than how to lay a value out.
 *
 * <p>Three values with nothing under them, which is why this is an enum rather than a sum. Which
 * module wrote it is on the identity the reader asked with, and a copy of it here would be a second
 * one that nothing holds to the first.
 */
public enum DeclaredBy {

    /** A module this compile checked. An output emitting this program emits this declaration. */
    A_MODULE,

    /**
     * The language, in the reserved namespace, and no module of any compilation.
     *
     * <p>Nothing generates it: an output either ships an implementation of it by hand or generates
     * one, and which of the two is that output's own answer.
     */
    THE_LANGUAGE,

    /**
     * A module this compile read off the path — a dependency, already built.
     *
     * <p>What a value of one is made of is here, because this compile read it to check the module
     * that names it, and an output laying out such a value needs exactly what the checker did. What
     * an output does not do is emit it: the build that made that module emitted it already, and a
     * second one under the same name would be two definitions of one declaration.
     */
    A_MODULE_ON_THE_PATH
}
