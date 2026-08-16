package souther.compiler.meta;

/**
 * Whether two sets of declarations say the same thing about everything a value crossing between them
 * depends on.
 *
 * <p>More than two, because "they differ" and "it cannot be told" are different things to have found
 * out. A difference is established: both sides were read and one of them says something else, and
 * what to do about it is to build again. Being unable to tell is not a difference — nothing has been
 * established about the two at all — and a reader that reports it as one says a build is stale on
 * evidence it does not have. Which is why the ways of not being able to tell are kept apart from
 * each other too: a set of declarations that could not be read carries why, and an answer that never
 * said which build it reads by is not a reading that failed.
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
     * Whether they agree could not be established, because a set of declarations could not be read.
     *
     * <p>Not a disagreement. The classes may well be of exactly the module being evaluated; what is
     * known is that nothing here can say so, and a run that went ahead would be running rows against
     * something it was unable to check.
     *
     * <p>What could not be read is carried as the reading answered it, and the module it is about
     * comes from inside that answer. Named beside it here as well, the two would be a pair nothing
     * holds together — a module said to be unreadable while the reading that says so is about
     * another. Only a reading that has nothing to hand over is a reason to be here at all, which is
     * why it is that type and not a whole {@link Readback}: given one that is ready, this would be
     * a refusal built around a reading that succeeded.
     *
     * @param side which of the two could not be read, because what a reader does about it is not the
     *             same. Declarations the answer brings are the answer's build to fix; declarations
     *             this compile reads are its own path, and reporting that as the answer's would send
     *             someone to rebuild the one thing that is not in question
     */
    record Unreadable(Readback.NotReady<?> reading, Side side) implements Agreement {

        public Unreadable {
            java.util.Objects.requireNonNull(reading,
                    "what could not be read is the reading that could not be made");
            java.util.Objects.requireNonNull(side, "declarations belong to one side or the other");
        }

        /** The module whose declarations could not be read — the reading's answer, not a second
         *  name kept beside it. */
        public String module() {
            return reading.module();
        }
    }

    /**
     * The answer did not say which declarations it reads a row's values by.
     *
     * <p>Told apart from a reading that could not be read, because it is not one: nothing was read
     * and there was nothing to read. Saying which build it answers by is the whole of what an answer
     * of another build is asked, and the accessor is abstract so that an implementation which does
     * not say it is refused where it is written. What is left is one that answers with nothing,
     * which no reading turns into a second set of declarations.
     *
     * <p>Here rather than raised, and not read as the compile's own. An answerer is written outside
     * this package, so its answering with nothing is a thing to be refused rather than a state of
     * this compiler — raised, it would stop a compile over one implementation; taken for the
     * compile's own, an implementation would be out of the question by returning null.
     */
    record NoOriginStated(String module) implements Agreement {}

    /** Whose declarations could not be read. */
    enum Side {
        /** The ones the answer brings. */
        THE_ANSWER,
        /** The ones the module being evaluated is read by — this compile's own, or its path's. */
        THE_MODULE_BEING_EVALUATED
    }
}
