package souther.compiler.ast;

/**
 * What a definition of a module was made as, which is what decides the rules it is held to.
 *
 * <p>A module's fns do not all come from a {@code let}. A pass mints one to carry the value a row
 * writes at a position, so that the row runs its own operand the way the module runs its own body;
 * and a module emits a definition another module wrote, under the name it reaches it by, because
 * the artifact has to carry a method for it. Those two are unlike in every way a rule cares about,
 * and both arrive without a spelling — {@link Hir.FnDef#reachedAs} mints a name for the second
 * precisely because a reach name is not the declaration's name.
 *
 * <p>So {@link WrittenName#authored} cannot tell them apart, and a rule that asked it was asking
 * about the name when what it meant was the definition. What is asked here instead is what the
 * definition is. A definition that stands at a row's position carries the position, so a rule with
 * a question about that position — what it contributes to reading the value, whether it requires
 * the value to be of its type — asks the position rather than a set of names kept beside the tree.
 *
 * <p>Two cases and not a taxonomy of everything a pass may mint. What divides them is whether the
 * definition is a row's value, because that is the division the rules are about; a definition
 * another module declared is ordinary here and says which module wrote it in the one place that
 * answers that ({@link Hir.FnDef#declaredIn}).
 */
public sealed interface DefinitionRole {

    /** A definition read as a definition: a {@code let} its module wrote, and one another module
     *  wrote that this one emits. */
    record Ordinary() implements DefinitionRole {

        /** The one of these there is. A role holds nothing here, so a second instance would be a
         *  second name for one answer. */
        public static final Ordinary INSTANCE = new Ordinary();
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
    }
}
