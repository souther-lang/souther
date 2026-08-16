package souther.compiler.meta;


import java.util.List;
import java.util.Objects;

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
 * <p>What a reading answers with when it gets to the end is the type argument, because reading a
 * module is done in more than one stage and the stages end in different things. What one answers
 * without a universe is a module and its declarations ({@link ReadableModule}); what the next one
 * answers, with the modules around it in sight, is that module resolved
 * ({@link PublishedUniverse.Read}). The three states are the same three either way, and that is why
 * they are written once: a stage whose absences were its own would name some of the reasons and
 * leave the rest to a null, which is what happened — every refusal that needed a universe to be
 * found had nowhere to be said, so which reason a reader was given followed from which stage
 * happened to find it.
 *
 * <p>Nothing here throws for an artifact this compiler will not read. What is left of a raise is a
 * fault in the compiler, which is what a raise ought to mean, and a reader no longer has to decide
 * how wide to catch in order to tell the two apart.
 */
public sealed interface Readback<T> {

    /**
     * They carry a module this compiler read, with its import lines read as well.
     *
     * <p>The value is there. A reading that got to the end and answered with nothing would be a
     * fourth state wearing the name of the first — "it was read" and "there is something to read"
     * would come apart, and every reader switching on the three would take one for the other.
     */
    record Ready<T>(T value) implements Readback<T> {

        public Ready {
            Objects.requireNonNull(value, "a ready reading has a value");
        }
    }

    /**
     * What a reading answers when there is nothing to hand over.
     *
     * <p>Told apart from {@link Ready} as a type, so that a reader interested only in the absence —
     * one holding two readings against each other, which has nothing to say while either of them
     * can still be read — can be given the absence and not the reading. Handed the whole
     * {@code Readback}, such a reader could be built around a {@link Ready}, which is a state it
     * has no meaning for.
     *
     * <p>Each says which module it is about. The name is the one thing there is to say when there
     * is nothing else, so it belongs to the answer rather than to whoever is passing it on: kept
     * beside one instead, two names would travel together and nothing would say they are one name.
     */
    sealed interface NotReady<T> extends Readback<T> {

        /** The module this is about — the one authority for its name. */
        String module();

        /** These classes carry nothing for the name: no class of it, or one this compiler put no
         *  declarations on. Not the same as carrying something unreadable, and an importer is told
         *  different things about the two. */
        record SaysNothing<T>(String module) implements NotReady<T> {

            public SaysNothing {
                Objects.requireNonNull(module, "a reading is about a module");
            }
        }

        /** They carry a module this compiler will not read, and why.
         *
         * @param module the module the classes name
         * @param why    what went wrong, which is never nothing: an artifact refused for a reason
         *               nobody can name is what this whole type exists to stop
         */
        record Unreadable<T>(String module, Failure why) implements NotReady<T> {

            public Unreadable {
                Objects.requireNonNull(module, "a reading is about a module");
                Objects.requireNonNull(why, "a module this compiler will not read has a reason");
            }
        }

        /**
         * The same absence, as the answer of a reading whose success is something else.
         *
         * <p>A stage that cannot go on answers with what the stage before it found, and what that
         * stage would have answered with is not what this one would. Rebuilt rather than cast: the
         * switch is over every state there is, so a state added later is a compile error here
         * rather than one carried across by a cast that reads every value alike.
         */
        default <U> NotReady<U> asTheAnswerOf() {
            return switch (this) {
                case SaysNothing<?> nothing -> new SaysNothing<>(nothing.module());
                case Unreadable<?> unreadable ->
                        new Unreadable<>(unreadable.module(), unreadable.why());
            };
        }
    }

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
         * One of its classes carries metadata this compiler cannot read.
         *
         * <p>The one failure found before anything about Souther has been read. It is still a fact
         * about the artifact and not about the author's dependency list, which is why it is here and
         * not an absence — read as one, the author is told there is no such module while their build
         * file says otherwise.
         */
        record UnreadableMetadata() implements Failure {}

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
        }

        /**
         * Its declarations are not a set of declarations one module may have.
         *
         * <p>A published module can carry such a set: it was published under the rules of the
         * compiler that built it, and a rule this one has that that one did not is broken by an
         * artifact nobody here can edit. Which is what makes it a fact about the artifact rather
         * than a report — indexing this module's declarations is refused, so there is no module
         * here to have declarations at all.
         *
         * <p>At least one, and the type says so, for the reason {@link InvalidExposure} says it.
         */
        record InvalidDeclarations(DeclarationRejection first, List<DeclarationRejection> rest)
                implements Failure {

            public InvalidDeclarations {
                java.util.Objects.requireNonNull(first,
                        "a declarations failure is at least one declaration");
                rest = List.copyOf(rest);
            }
        }
    }

    /**
     * One declaration of an artifact that this compiler will not index, as a fact about the
     * artifact.
     *
     * <p>The same shape as {@link Exposure}, and here for the same reason. What the indexing finds
     * is a refusal carrying the declaration it refused — an AST node, with the place in the
     * published text it was parsed from — and the place is in a text nobody holds. So the refusal is
     * projected here, and what crosses is which declaration and which rule.
     *
     * <p>Told apart from the reasons a readback fails, because the two are at different
     * granularities and about different things: a {@link Failure} says which part of reading an
     * artifact did not hold, and this says what is wrong with the declarations it carries. Flattened
     * into {@code Failure}, the reasons a set of declarations can be refused would be arms of the
     * type that says how far a reading got.
     */
    sealed interface DeclarationRejection {

        /** The declaration this is about. */
        String declaration();

        /** The module declares the name twice. */
        record DeclaredTwice(String declaration) implements DeclarationRejection {}

        /** It is named after a built-in {@code Option} case, which no module may declare
         *  (ADR-0035). */
        record BuiltInOptionCaseDeclared(String declaration) implements DeclarationRejection {}
    }

    /**
     * One import line of an artifact that could not do its job, as a fact about the artifact.
     *
     * <p>A refusal is the same failure as the check that reads a source finds it, and carries the
     * {@code import} line it was written on so that a reader with that source can quote it. Carried
     * across this boundary it would bring a position in a text nobody holds — which is the defect
     * this whole type exists to close, arriving as an AST node instead of as a diagnostic. So the
     * refusal is projected here, and what crosses is what happened and not where.
     *
     * <p>Kept apart from the reasons a readback fails, because the two are read at different
     * granularities: an artifact is unreadable or it is not, and its import lines are however many
     * they are.
     */
    sealed interface Exposure {

        /** The library module the line names. */
        String from();

        /** The name it was to bring in. */
        String name();

        /** The standard library publishes no operation of that name in that module. */
        record NoSuchLibraryFunction(String from, String name) implements Exposure {}
    }
}
