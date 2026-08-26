package souther.compiler.program;

/**
 * Which of the two worlds declared a data: a module of this compilation, or the language itself.
 *
 * <p>Provenance and nothing else. Whether the snapshot holds what a value of it is made of is
 * {@link Declared}'s question and is answered by which arm carries this, so nothing here says
 * anything about where the declaration was found.
 *
 * <p>Two values with nothing under them, which is why this is an enum rather than a sum: a module's
 * declaration and the language's differ in who wrote them and in nothing a reader is handed. Which
 * module wrote it is on the identity the reader asked with, and a copy of it here would be a second
 * one that nothing holds to the first.
 */
public enum DeclaredBy {

    /** A module this compile checked. What such a declaration is called on a machine, and what
     *  emits it, is the emitting output's own. */
    A_MODULE,

    /**
     * The language, in the reserved namespace, and no module of any compilation.
     *
     * <p>It resolves and types like a module's own and a value of it lays out like one, which is why
     * it is read the same way. What differs is that nothing generates it: an output either ships an
     * implementation of it by hand or generates one, and which of the two is that output's answer.
     */
    THE_LANGUAGE
}
