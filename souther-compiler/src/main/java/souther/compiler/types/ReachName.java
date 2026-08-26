package souther.compiler.types;

/**
 * A resolved reference: the route a module reaches a definition by, and what it reaches.
 *
 * <p>Held together, and not as a spelling. A caller with only the rendering has the half that
 * cannot be looked anything up with, and a caller with only the declaration has the half that
 * cannot say how this module got to it; a pass that carried one of them alone recovers the other by
 * resolving a spelling, which is the rediscovery this exists to stop. {@link TypeReachName} is the
 * same value for the type namespace and says the same thing.
 *
 * <p>The route is not the declaration's identity. Which module declares something is a fact about
 * the declaration and is {@link ValueName}'s to say; which arm this is, is a fact about the
 * reference. {@code souther.list} declares {@code foldFrom} and a reader reaches it as
 * {@code List.foldFrom}: the alias belongs to the reference and the declaring module is nowhere in
 * it. So the two are one value with two questions, and neither is recovered from a string.
 *
 * <p>What it renders as follows from both, and is answered here rather than stored. A rendering
 * kept beside the declaration is a second statement of the same thing, and the day one of them is
 * written from a different reading they disagree with nothing to say so.
 *
 * <p>Settled where a name is resolved, which is the one place that has both what the name denotes
 * and the module doing the reading. Every pass after that carries it, and none works it out again
 * from a spelling: a reader that took the spelling would answer one thing before the pass that
 * writes imported names qualified and another after — silently, because a miss is what a table does
 * with a key it has not got.
 *
 * <p>Two references are the same reference when they take the same route to the same declaration.
 * Rendering alike is not being the same: two bindings of one spelling render alike and denote
 * different bindings, and a reference is not made one by how it looks.
 *
 * <p>The interface is sealed and the switches over it carry no {@code default}, so a shape added here
 * is a compile error at every place that reads one rather than something quietly taken for another.
 */
public sealed interface ReachName {

    /** What this reference reaches. */
    ValueName denotes();

    /** The spelling this route reaches it by — what a report quotes, and what a name built for a
     * machine is built from. Never what a source wrote: the source may write a module's own
     * behavior through its own module, and this is what the module reaches it by. */
    String rendered();

    /**
     * A name reached as it stands: what the module declares itself, a binding in force, a behavior it
     * can call, a type used as a value.
     *
     * <p>What these have in common is that no qualifier gets between the reference and what it
     * reaches, so the declaration's own name is the whole of it.
     */
    record Bare(ValueName denotes) implements ReachName {

        public Bare {
            if (denotes == null) {
                throw new IllegalArgumentException("a reference reaches something");
            }
        }

        @Override
        public String rendered() {
            return denotes.name();
        }

        @Override
        public String toString() {
            return rendered();
        }
    }

    /**
     * A definition another module declares, reached under that module's name.
     *
     * <p>Here the route's rendering is built out of the declaration's own module and name, and that
     * is a property of this route rather than of declarations — {@link OfLibrary} reads the same
     * declaration and renders it under an alias the declaration knows nothing about.
     */
    record OfModule(ValueName.OfAModule denotes) implements ReachName {

        public OfModule {
            if (denotes == null) {
                throw new IllegalArgumentException("a reference reaches something");
            }
        }

        @Override
        public String rendered() {
            return denotes.module() + "." + denotes.name();
        }

        @Override
        public String toString() {
            return rendered();
        }
    }

    /**
     * A standard-library name, reached under the alias the library publishes it under.
     *
     * <p>The denotation says which of the library's two shapes this is — an operation of a module it
     * publishes, or the module applied as a constructor ({@code Date("2026-09-30")}) — so the route
     * needs nothing beside it.
     */
    record OfLibrary(ValueName.Stdlib denotes) implements ReachName {

        public OfLibrary {
            if (denotes == null) {
                throw new IllegalArgumentException("a reference reaches something");
            }
        }

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
     * How {@code denotes} is reached from {@code self}, where it was written {@code written}.
     *
     * <p>The one place a reach name is worked out. It takes the module doing the reading because that
     * is what decides the answer for a helper: the module's own is reached bare and another's under
     * the module that declares it, and neither the declaration nor the spelling says which case this
     * is on its own.
     *
     * <p>{@code written} decides nothing and is here to be quoted where this is refused. A module's
     * own behavior written through its own module is reached bare, and an import lets another
     * module's be written bare and it is reached under the module that declares it — so a route read
     * off the spelling is a route that changes when an author qualifies a name.
     *
     * <p>Asked only of a name that denotes something. One nothing declares is
     * {@link souther.compiler.ast.Hir.Var.Unanswered}, which reaches nothing and is not asked; it
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
                    ? new Bare(helper) : new OfModule(helper);
            // A behavior is declared by a module, so it is reached the two ways a helper is, and
            // the answer is read off the declaration rather than off the spelling. Written it can
            // be either — a module's own behavior may be written through its own module, and
            // another's may be written bare where an import brought it in — and neither spelling
            // says which module declares what it reaches.
            case ValueName.Behavior behavior -> behavior.module().equals(self)
                    ? new Bare(behavior) : new OfModule(behavior);
            case ValueName.Stdlib library -> new OfLibrary(library);
            // Each of these is reached by the name it is bound or written under, which is the name
            // the denotation carries: a binding is named where it is bound, and a type used as a
            // value by what this module calls it.
            case ValueName.Local _, ValueName.OfType _, ValueName.Builtin _ -> new Bare(denotes);
        };
    }

}
