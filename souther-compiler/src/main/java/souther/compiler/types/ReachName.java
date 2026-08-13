package souther.compiler.types;

/**
 * The name a module reaches a definition by, from the place that named it.
 *
 * <p>Not the definition's identity. Which module declares something is a fact about the declaration
 * and is written there ({@code Ast.FnDef#declaredIn}); this is a fact about the reference, and the two
 * cannot be derived from each other. {@code souther.list} declares {@code foldFrom} and a reader
 * reaches it as {@code List.foldFrom}: the alias belongs to the reference, and the declaring module is
 * nowhere in it.
 *
 * <p>Settled where a name is resolved, which is the one place that has both what the name denotes and
 * the module doing the reading. Every pass after that carries it, and none works it out again from a
 * spelling: a reader that took the spelling would answer one thing before the pass that writes
 * imported names qualified and another after — silently, because a miss is what a table does with a
 * key it has not got.
 *
 * <p>The interface is sealed and the switches over it carry no {@code default}, so a shape added here
 * is a compile error at every place that reads one rather than something quietly taken for another.
 */
public sealed interface ReachName {

    /** The spelling this reach name is written as — what a table keyed by names is looked up with,
     * and what a report quotes where it has nothing better. */
    String rendered();

    /**
     * A name reached as it stands: what the module declares itself, a binding in force, a behavior it
     * can call, a type used as a value.
     *
     * <p>What these have in common is that no qualifier gets between the reference and what it
     * reaches, so the name is the whole of it.
     */
    record Bare(String name) implements ReachName {

        @Override
        public String rendered() {
            return name;
        }

        @Override
        public String toString() {
            return name;
        }
    }

    /**
     * A definition another module declares, reached under that module's name.
     *
     * <p>Here the reach name and the declaration's identity do coincide, and they coincide by
     * accident of how a user module is reached rather than by rule — {@link OfLibrary} is the same
     * relation with a different answer, and is what shows the two are separate values.
     */
    record OfModule(String module, String name) implements ReachName {

        @Override
        public String rendered() {
            return module + "." + name;
        }

        @Override
        public String toString() {
            return rendered();
        }
    }

    /**
     * A standard-library name, reached under the alias the library publishes it under.
     *
     * <p>It holds the denotation rather than an alias and a name of its own: the library already says
     * which of its two shapes this is — an operation of a module it publishes, or the module applied
     * as a constructor ({@code Date("2026-09-30")}) — and copying that distinction into a second
     * optional field here would be the same fact written twice.
     */
    record OfLibrary(ValueName.Stdlib target) implements ReachName {

        @Override
        public String rendered() {
            return target.qualified();
        }

        @Override
        public String toString() {
            return rendered();
        }
    }

    /**
     * How {@code denotes} is reached from {@code self}, where it was written {@code written}.
     *
     * <p>The one place a reach name is worked out. It takes the module doing the reading because that
     * is what decides the answer for a helper: the module's own is reached bare and another's under
     * the module that declares it, and neither the declaration nor the spelling says which case this
     * is on its own.
     *
     * <p>Asked only of a name that denotes something. One nothing declares is
     * {@link souther.compiler.ast.Ast.Var.Unanswered}, which reaches nothing and is not asked; it
     * used to be answered with its own spelling, and a spelling handed back as a reach name is a
     * reference that reaches whatever the reading module happens to mean by it (ADR-0067). A caller
     * with no denotation at hand has not resolved one yet, and is refused for the same reason.
     */
    static ReachName of(ValueName denotes, String written, String self) {
        if (self == null) {
            throw new IllegalArgumentException("which module is reading decides this: " + written);
        }
        if (denotes == null) {
            throw new IllegalArgumentException("`" + written
                    + "` has not been resolved, so nothing here says how it is reached");
        }
        return switch (denotes) {
            case ValueName.Helper helper -> helper.module().equals(self)
                    ? new Bare(helper.name()) : new OfModule(helper.module(), helper.name());
            case ValueName.Stdlib library -> new OfLibrary(library);
            // Each of these is reached by the name it is written with: a binding is named where it
            // is bound, and a behavior and a type by what this module calls them.
            case ValueName.Local _, ValueName.Behavior _, ValueName.OfType _,
                    ValueName.Builtin _ -> new Bare(written);
        };
    }

}
