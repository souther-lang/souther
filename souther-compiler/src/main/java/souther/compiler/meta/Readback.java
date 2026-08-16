package souther.compiler.meta;


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

        /**
         * What the class carries declares a different module.
         *
         * <p>Which module a reading is about is the name it was asked for; which module the
         * declarations are of is what their header says. The class is found by the first and the
         * module is named by the second, and nothing held the two together — so an artifact whose
         * header names something else came back as a module filed under a name that is not its own,
         * with every question about it answered from the wrong declarations.
         *
         * @param named the name the artifact gave itself
         */
        record AnotherModule(String named) implements Failure {}

        /**
         * There is a class of that name and this JVM does not read class files of its kind: a
         * malformed one, or one at a major version it does not know.
         *
         * <p>The one failure found before anything about Souther has been read. It is still a fact
         * about the artifact and not about the author's dependency list, which is why it is here and
         * not an absence — read as one, the author is told there is no such module while their build
         * file says otherwise.
         */
        record NotClassFilesThisJvmReads() implements Failure {}

        /** What was published is not source this compiler parses.
         *
         * <p>Nothing about where. The text was put back together here out of what the module
         * carries, so a line of it is a line of nothing anybody holds, and the author reading this
         * cannot go there or edit it either way — what there is to do about it is rebuild the
         * artifact, which the module's name is enough to say. */
        record InvalidPublishedSyntax() implements Failure {}

        /**
         * Its import lines could not do their job.
         *
         * <p>At least one, and the type says so: {@code first} is the one a reader with room for a
         * single sentence says, and there is no way to build this with nothing in it. A caller
         * reading the head of a list it was told is non-empty by a comment is a caller the next
         * producer can break.
         */
        record InvalidExposure(Exposure first, List<Exposure> rest) implements Failure {

            public InvalidExposure {
                java.util.Objects.requireNonNull(first, "an exposure failure is at least one line");
                rest = List.copyOf(rest);
            }

            /** All of them, the first included, in the order the lines are written. */
            public List<Exposure> all() {
                List<Exposure> every = new java.util.ArrayList<>();
                every.add(first);
                every.addAll(rest);
                return List.copyOf(every);
            }
        }
    }

    /**
     * One import line of an artifact that could not do its job, as a fact about the artifact.
     *
     * <p>{@link Exposing.Refusal} is the same failure as the check that reads a source finds it, and
     * carries the {@code import} line it was written on so that a reader with that source can quote
     * it. Carried across this boundary it would bring a position in a text nobody holds — which is
     * the defect this whole type exists to close, arriving as an AST node instead of as a
     * diagnostic. So the refusal is projected here, and what crosses is what happened and not where.
     *
     * <p>Kept apart from the reasons a readback fails, because the two are read at different
     * granularities: an artifact is unreadable or it is not, and its import lines are however many
     * they are.
     */
    public sealed interface Exposure {

        /** The library module the line names. */
        String from();

        /** The name it was to bring in. */
        String name();

        /** The standard library publishes no operation of that name in that module. */
        record NoSuchLibraryFunction(String from, String name) implements Exposure {}

        /** Two library modules publish the bare name, so importing both leaves it saying neither. */
        record BroughtTwice(String from, String name, String earlier) implements Exposure {}

        /** The name is also declared by the module the line is written in. */
        record CollidesWithADeclaration(String from, String name) implements Exposure {}
    }
}
