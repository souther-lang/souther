package souther.compiler.types;

/**
 * What a name written in the value namespace denotes — the answer {@link TypeName} gives for the
 * type namespace.
 *
 * <p>A behavior is named from a {@code >->} stage and from a {@code requires} clause, bare or
 * qualified, and whether two spellings mean one behavior was a question each consumer used to answer
 * for itself. Resolution answers it once, in {@link souther.compiler.query.Names.Bound}, and every
 * name-bearing position carries the answer from there on.
 *
 * <p>The interface is sealed and the switches over it carry no {@code default}, so a case added here
 * is a compile error at every place that reads one rather than something silently taken for another.
 */
public sealed interface ValueName {

    /** The bare name, which is what a behavior is reached by wherever it was declared. */
    String name();

    /** A behavior, and the module that declares it. */
    record Behavior(String module, String name) implements ValueName {

        public Behavior {
            if (module == null || name == null) {
                throw new IllegalArgumentException("module and name are required: " + module + "."
                        + name);
            }
        }

        @Override
        public String toString() {
            return module + "." + name;
        }
    }

    /**
     * A name nothing denotes, keeping the spelling that was written.
     *
     * <p>Why it denotes nothing was reported where it was written, so a reader that meets one says
     * nothing further: the definition resting on it is abandoned, and the definitions around it are
     * checked as they would be without it. This is what {@link TypeName#unresolved} is for a type.
     */
    record Unresolved(String written) implements ValueName {

        @Override
        public String name() {
            return written;
        }

        @Override
        public String toString() {
            return written;
        }
    }
}
