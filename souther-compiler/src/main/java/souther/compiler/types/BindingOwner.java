package souther.compiler.types;

/**
 * What a binding belongs to — the definition whose text introduced it, or the copy of a body that a
 * pass placed inside one.
 *
 * <p>An owner is named by what already identifies a definition across the whole compiler: the
 * declaring module and the name declared there, which is what {@link TypeName} is for a type. None of
 * them is a bare spelling, so neither is a {@link BindingId}: two modules that both declare
 * {@code f} own different bindings, and saying so needs no comparison of text.
 *
 * <p>The interface is sealed and the switches over it carry no {@code default}, so a case added here
 * is a compile error at every place that reads one.
 */
public sealed interface BindingOwner {

    /** The module that declares what this belongs to. A copy is owned where it was placed, so it
     * answers with the module that reads it rather than the one the body was written in. */
    default String module() {
        return switch (this) {
            case OfValue v -> v.module();
            case OfData d -> d.declared().module();
            case Expansion e -> e.within().module();
            case Synthesized s -> s.within().module();
        };
    }

    /**
     * The body of a value definition: a module's own {@code let}, or a behavior's implementation.
     *
     * <p>Which of the two it is says nothing about identity, because a module cannot declare both
     * under one name — a {@code let} whose name a behavior declares <em>is</em> that behavior's
     * implementation. So the pair names the definition, as {@link TypeName} names a declared type.
     */
    record OfValue(String module, String name) implements BindingOwner {

        public OfValue {
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

    /** What a data declaration writes for itself: an invariant, a decoder, an encoder. */
    record OfData(TypeName declared) implements BindingOwner {

        @Override
        public String toString() {
            return declared.toString();
        }
    }

    /**
     * A copy of {@code expanded}'s body, placed inside {@code within}.
     *
     * <p>Expanding a helper puts a second copy of its bindings in one body, so the copy owns them
     * rather than the definition they were written in: a binding of the original keeps the ordinal it
     * was given and changes owner. {@code ordinal} tells apart two expansions of the same thing in
     * one place, so adding an expansion elsewhere moves nothing here, and an expansion inside an
     * expansion is told apart by {@code within} without anything counting across the two.
     */
    record Expansion(BindingOwner within, ValueName expanded, int ordinal) implements BindingOwner {


        @Override
        public String toString() {
            return within + "/" + expanded + "#" + ordinal;
        }
    }

    /** Bindings {@code pass} made inside {@code within}, which no source wrote. */
    record Synthesized(BindingOwner within, Pass pass, int ordinal) implements BindingOwner {

        @Override
        public String toString() {
            return within + "/" + pass + "#" + ordinal;
        }
    }

    /** The passes that introduce a binding of their own. Named here rather than by each pass, so
     * that what may mint one is a closed list. */
    enum Pass { DERIVER, NEWTYPE_DESUGAR, HELPER_PARAMS, INLINER, LOWER }
}
