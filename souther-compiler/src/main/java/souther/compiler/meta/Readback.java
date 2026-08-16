package souther.compiler.meta;

import souther.compiler.check.Exposing;

import java.util.List;

/**
 * What reading one module back off a set of published classes answers.
 *
 * <p>Three states and no fourth. These classes say nothing about the name; they say something this
 * compiler read and checked; they say something it will not read. A reader that has one of these has
 * been told which, and there is no way to hold a module that has not been checked — the decoded
 * declarations exist only inside the reading, and nothing hands them out.
 *
 * <p>That is the whole point of the type. A reader used to get the declarations back and check the
 * import lines itself, so "decoded" and "usable" were the same value and a reader that did the first
 * and not the second held a module whose bare names denoted nothing. One did, in every project but
 * the one that wrote it.
 *
 * <p>Nothing here throws for an artifact this compiler will not read. What is left of a raise is a
 * fault in the compiler, which is what a raise ought to mean, and a reader no longer has to decide
 * how wide to catch in order to tell the two apart.
 */
public sealed interface Readback {

    /** These classes carry nothing for the name: no class of it, or one this compiler put no
     *  declarations on. Not the same as carrying something unreadable, and an importer is told
     *  different things about the two. */
    record SaysNothing() implements Readback {}

    /** They carry a module this compiler read, with its import lines read as well. */
    record Ready(ReadableModule module) implements Readback {}

    /** They carry a module this compiler will not read, and why.
     *
     * @param module the module the classes name — the one authority for it, the failure saying only
     *        what went wrong
     */
    record Unreadable(String module, Failure why) implements Readback {}

    /**
     * Why a module this compiler knows the classes carry could not be read.
     *
     * <p>Semantic facts and nothing else. No diagnostic, no exception, no position: where a report
     * about this is said, and what it quotes, is settled by whoever holds a source to send a reader
     * to, and a place carried from inside the artifact would be a line of a text nobody holds. This
     * is what happened while these were raises — the author of an importing project was shown line 2
     * of a module they do not have.
     *
     * <p>Closed, so that what converts is stated rather than guessed at a catch. Every arm is a
     * failure this compiler knows the shape of; anything else that goes wrong reading an artifact is
     * a fault, and stays one.
     */
    sealed interface Failure {

        /** The declarations are recorded at a boundary revision this compiler does not agree with,
         *  or carry no header at all, which comes to the same thing.
         *
         * @param compiler what the artifact says built it */
        record Incompatible(String compiler) implements Failure {}

        /** The module names a declaration whose class these classes do not carry: the jar it came
         *  from is incomplete.
         *
         * @param declaration the type or behavior that was named */
        record DeclarationMissing(String declaration) implements Failure {}

        /** What was published is not source this compiler parses.
         *
         * <p>Nothing about where. The text was put back together here out of what the module
         * carries, so a line of it is a line of nothing anybody holds, and the author reading this
         * cannot go there or edit it either way — what there is to do about it is rebuild the
         * artifact, which the module's name is enough to say. */
        record InvalidPublishedSyntax() implements Failure {}

        /** Its import lines could not do their job, as the check that reads them found them.
         *
         * <p>The refusals travel as they were found rather than as sentences about them. The same
         * failures on a line of a source this compilation holds are said on that line; here there is
         * no line to say them on, and turning them into diagnostics in order to carry them would put
         * a place on them that has to be taken off again. */
        record InvalidExposure(List<Exposing.Refusal> refusals) implements Failure {

            public InvalidExposure {
                refusals = List.copyOf(refusals);
            }
        }
    }
}
