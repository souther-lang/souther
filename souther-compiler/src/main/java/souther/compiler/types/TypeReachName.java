package souther.compiler.types;

/**
 * How a module writes a declared type — the answer {@link ReachName} gives for the value namespace.
 *
 * <p>Not the type's identity. Which module declares a type is a fact about the declaration and is
 * {@link TypeName}'s to say; this is a fact about a reference to it from somewhere, and neither can
 * be derived from the other. One {@code lib.Amount} is written {@code Amount} in a module that
 * imported it, {@code up.Amount} in one that aliased {@code lib} as {@code up}, and
 * {@code lib.Amount} in one that did neither — three references, one declaration.
 *
 * <p>Held together with what it denotes, and not as a string. A caller with only the rendering has
 * the half that cannot be looked anything up with, and a caller with only the name has the half that
 * cannot be written into anything a person reads; a pass that carried one of them alone is the
 * defect this exists to remove, since the two are recovered from each other by resolving a spelling
 * — which is the rediscovery {@link ReachName} was separated out to stop.
 *
 * <p>Having a spelling at all is one of the answers. A module reaches a sum through its declaring
 * module and the cases that sum lists through the sum, so a case its module does not expose is a
 * value of a position here that nothing here can name. That is a state of the reference and is held
 * as one: only {@link Written} has a {@link Written#rendered()}, so a caller that would write the
 * name has to say what it does where there is none, rather than being handed a spelling that
 * resolves to nothing wherever it is put.
 *
 * <p>The interface is sealed and the switches over it carry no {@code default}, so a shape added
 * here is a compile error at every place that reads one.
 */
public sealed interface TypeReachName {

    /** The declaration this reference reaches. */
    TypeName denotes();

    /** A reference this module can write. */
    sealed interface Written extends TypeReachName {

        /** The reference as this module writes it — what goes into anything an author reads back,
         * and what the reader of the position it is written at answers {@link #denotes()} for. */
        String rendered();
    }

    /**
     * A type written as its bare name: one the module declares itself, or one an import brought in
     * under that spelling.
     *
     * <p>Bare only where the bare spelling means <em>this</em> declaration. A module that declares
     * an {@code Amount} of its own and imports another module's under an alias writes the imported
     * one qualified, and a reference that took the bare spelling because the name was in scope would
     * name the wrong declaration and compile.
     */
    record Bare(TypeName denotes) implements Written {

        @Override
        public String rendered() {
            return denotes.name();
        }

        @Override
        public String toString() {
            return rendered();
        }
    }

    /** A type reached under an {@code import ... as} alias, which names a module and is not one. */
    record ViaAlias(String alias, TypeName denotes) implements Written {

        public ViaAlias {
            if (alias == null) {
                throw new IllegalArgumentException("an alias is what this is reached under: "
                        + denotes);
            }
        }

        @Override
        public String rendered() {
            return alias + "." + denotes.name();
        }

        @Override
        public String toString() {
            return rendered();
        }
    }

    /** A type reached under the name of the module that declares it — what is left where the module
     * neither declares it, imports it, nor aliases the module it comes from. */
    record ViaModule(TypeName denotes) implements Written {

        @Override
        public String rendered() {
            return denotes.qualified();
        }

        @Override
        public String toString() {
            return rendered();
        }
    }

    /**
     * Nothing here names it: the module that declares it does not expose it, so no spelling reaches
     * it from here — not the bare name, and not the qualified one either.
     *
     * <p>A value of it can still stand at a position here. A sum is reached through its module and
     * its cases through the sum, so a behavior takes a value of a case it cannot name and a decoder
     * builds one; what cannot happen is a person writing that value down, which is what a generated
     * row is for.
     */
    record Unnameable(TypeName denotes) implements TypeReachName {

        @Override
        public String toString() {
            return "no name for " + denotes + " here";
        }
    }

    /**
     * Whatever answers this for a module — {@code Symbols}, which holds what the module's bare names
     * mean and which modules its aliases name.
     *
     * <p>Taken as an argument by anything that writes a reference it did not read, so that the
     * question is asked of the module rather than answered from the declaration's own spelling. A
     * writer that could reach for {@link TypeName#name()} instead is a writer that answers it wrong
     * wherever the bare spelling is not this module's word for the type.
     */
    @FunctionalInterface
    interface Naming {

        /** How the module this belongs to writes {@code type}. */
        TypeReachName of(TypeName type);
    }
}
