package souther.compiler.meta;

/**
 * Whether two sets of declarations say the same thing about everything a value crossing between them
 * depends on.
 *
 * <p>Three answers and not two, because "they differ" and "it cannot be told" are different things to
 * have found out. A difference is established: both sides were read and one of them says something
 * else, and what to do about it is to build again. Being unable to tell is not a difference — nothing
 * has been established about the two at all — and a reader that reports it as one says a build is
 * stale on evidence it does not have.
 */
public sealed interface Agreement {

    /** Nothing a crossing depends on differs. */
    record Agree() implements Agreement {}

    /**
     * One declaration says something else.
     *
     * <p>The first one found, and not all of them. What this is read for is that the two are of
     * different builds, which one declaration settles; going on to collect the rest would be
     * collecting the ways one stale build differs from a current one, which is a list nobody acts on
     * differently.
     *
     * @param module      the module the declaration is of, which is the one that moved rather than
     *                    the module the rows are written for — they are the same only where nothing
     *                    imported was what differed
     * @param declaration what it is called
     */
    record Disagree(String module, String declaration) implements Agreement {}

    /**
     * Whether they agree could not be established.
     *
     * <p>Not a disagreement. The classes may well be of exactly the module being evaluated; what is
     * known is that nothing here can say so, and a run that went ahead would be running rows against
     * something it was unable to check.
     */
    record Unreadable(String module, Reason reason) implements Agreement {}

    /** Why declarations could not be read back. */
    enum Reason {

        /**
         * Nothing was published for the module: no class carries its declarations.
         *
         * <p>A jar from before modules carried them is one way to arrive here, and a name that is
         * not a compiled Souther module at all is another. Neither can be told from the other, and
         * neither leaves anything to compare.
         */
        NOTHING_PUBLISHED,

        /**
         * A module was published and this compiler cannot read what it published: the declarations
         * were written at another boundary revision, or the classes carrying them are not all there.
         *
         * <p>One reason and not two, because what a reader does about either is the same. What is
         * published travels as source and is read back by the front end, so what a jar promises is
         * recorded under {@link souther.compiler.codegen.Backend#BOUNDARY_VERSION} — and declarations
         * this compiler cannot read are not a stale build of the same model, they are a build it
         * cannot say anything about.
         */
        NOT_READABLE_HERE
    }
}
