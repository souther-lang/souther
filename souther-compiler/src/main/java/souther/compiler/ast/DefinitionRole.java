package souther.compiler.ast;

/**
 * What a definition of a module was made as, which is what decides the rules it is held to.
 *
 * <p>A module's fns do not all come from a {@code let}. A pass mints one to carry the value a row
 * writes at a position, so that the row runs its own operand the way the module runs its own body;
 * and a module emits a definition another module wrote, under the reference it reaches it by,
 * because the artifact has to carry a method for it. Those two are unlike in every way a rule cares
 * about, and both arrive without a spelling — {@link Hir.FnDef#reachedAs} mints a name for the
 * second precisely because a reach name is not the declaration's name, and keeps the reference so
 * that the declaration is not left to be read back out of that name.
 *
 * <p>So {@link WrittenName#authored} cannot tell them apart, and a rule that asked it was asking
 * about the name when what it meant was the definition. What is asked here instead is what the
 * definition is. A definition that stands at a row's position carries the position, so a rule with
 * a question about that position — what it contributes to reading the value, whether it requires
 * the value to be of its type — asks the position rather than a set of names kept beside the tree.
 *
 * <p>What divides these is whether the definition is the model's or the rows'. A definition another
 * module declared is the model's here and says which module wrote it in the one place that answers
 * that ({@link Hir.FnDef#declaredIn}); the other two are there so that rows can be written, and
 * {@link #isTheModels} is what a rule about the difference asks.
 */
public sealed interface DefinitionRole {

    /**
     * Whether the definition is the model's: what the module's own source declares, what a jar of
     * the module carries, and what another declaration of the model may name.
     *
     * <p>Answered by each case rather than by a test against one of them, so a case added later is
     * one somebody had to answer for. Read as "not a row's value" it would put every new case on
     * the model's side by default, which is the side that publishes and the side the model may
     * reach.
     */
    boolean isTheModels();

    /** A definition read as a definition: a {@code let} its module wrote in its own source. */
    record Ordinary() implements DefinitionRole {

        /** The one of these there is. A role holds nothing here, so a second instance would be a
         *  second name for one answer. */
        public static final Ordinary INSTANCE = new Ordinary();

        @Override
        public boolean isTheModels() {
            return true;
        }
    }

    /**
     * A value an attached file declares, for the rows written beside it to name.
     *
     * <p>An {@code examples for} file's values join the module its rows join, so from resolution
     * onwards they sit among the module's own definitions under one set of names. What tells them
     * apart is this, and not where their text is: whether a jar of the module happens to carry a
     * slice for one is how the artifact is written, and the question every rule here asks is whose
     * the declaration is.
     *
     * <p>Two rules read it. Such a value is not published — the model compiles to nothing of the
     * attached file, so there is no source of it in a jar to carry. And the model may not name one
     * (spec §an-attached-files-values-are-for-its-rows): the file is for the rows and the values
     * they name, and a model that reached into it would be a model its fixtures hold up.
     */
    record AttachedValue() implements DefinitionRole {

        /** The one of these there is, for the same reason {@link Ordinary#INSTANCE} is. */
        public static final AttachedValue INSTANCE = new AttachedValue();

        @Override
        public boolean isTheModels() {
            return false;
        }
    }

    /**
     * The value a row writes at {@code position}, compiled as a definition so that it runs in the
     * program the behavior it is about is applied in.
     *
     * <p>{@code position} is what the row's notation is read against and what the value may be
     * required to be. Carried rather than looked up: it is settled where this definition is made,
     * and a reader that had to find it again would be finding it by the definition's name.
     */
    record RowValue(RowPosition position) implements DefinitionRole {

        public RowValue {
            if (position == null) {
                throw new IllegalArgumentException("a row's value stands at a position");
            }
        }

        @Override
        public boolean isTheModels() {
            return false;
        }
    }

    /**
     * A definition another module declares, which this module emits as a method of its own because
     * a call to it was left standing.
     *
     * <p>{@code reachedAs} is the reference that call reaches it by, carried here rather than left
     * as the name the definition was renamed to. Which declaration this is a copy of is that
     * reference's to say and cannot be read back out of the renaming: {@code souther.list} declares
     * {@code foldFrom} and a module emits it under {@code List.foldFrom}, so a reader holding the
     * spelling has an alias and a name joined by a dot and no way to tell which part is which.
     *
     * <p>The model's, and declared elsewhere. Which module wrote it is {@link Hir.FnDef#declaredIn},
     * as it is for any definition; what is here is how this module got to it.
     */
    record TakenOn(souther.compiler.types.ReachName.Declaration reachedAs)
            implements DefinitionRole {

        public TakenOn {
            if (reachedAs == null) {
                throw new IllegalArgumentException(
                        "a definition emitted for a call is emitted for the reference that reached it");
            }
        }

        @Override
        public boolean isTheModels() {
            return true;
        }
    }
}
