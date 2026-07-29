package souther.compiler.types;

import souther.compiler.diag.SourcePos;

/**
 * What a name written in the value namespace denotes — the answer {@link TypeName} gives for the
 * type namespace.
 *
 * <p>A behavior is named from a {@code >->} stage and from a {@code depends on} clause; a body names a
 * local, a helper, a library function, an injected behavior, a type used as a value. Whether two
 * spellings mean one thing was a question each consumer used to answer for itself, in the order that
 * consumer happened to try. Resolution answers it once — a behavior name where the module's names are
 * bound, a name in a body where its bindings are known — and every name-bearing position carries the
 * answer from there on.
 *
 * <p>The interface is sealed and the switches over it carry no {@code default}, so a case added here
 * is a compile error at every place that reads one rather than something silently taken for another.
 */
public sealed interface ValueName {

    /** The bare name, which is what a definition is reached by wherever it was declared. */
    String name();

    /**
     * A name bound inside a body: a parameter, a {@code let}, a {@code match} arm's binding, or a
     * block's parameter. {@code binder} is where the binding that introduced it is written, which is
     * what tells two bindings of one spelling apart.
     */
    record Local(String name, SourcePos binder) implements ValueName {

        @Override
        public String toString() {
            return name;
        }
    }

    /** A module's own {@code let} — a helper, which is expanded into the body that called it. */
    record Helper(String module, String name) implements ValueName {

        @Override
        public String toString() {
            return module + "." + name;
        }
    }

    /**
     * A standard-library function, under the qualified name the library is keyed by
     * ({@code List.map}, {@code String.trim}). A prelude helper, a prelude intrinsic and a checker
     * built-in are one thing to a name: what is on the other side of the name is the library's own
     * business.
     */
    record Stdlib(String qualified) implements ValueName {

        @Override
        public String name() {
            return qualified;
        }

        @Override
        public String toString() {
            return qualified;
        }
    }

    /**
     * A type written where a value goes: a unit data as a value, or a newtype applied to the value
     * it wraps. Which of the two is decided by what the type is, not by how the name was written.
     *
     * <p>{@code publishedBy} is the module whose published value or helper carried this name here,
     * and null where the body being read wrote it. A unit data is *constructed* by being named, and
     * a construction says where it came from ({@link souther.compiler.ast.Ast.NewData}) so that the
     * permission check can tell the reader's own from one it was handed; a unit data has no node of
     * its own to say it on, so the name says it.
     */
    record OfType(String name, TypeName type, String publishedBy) implements ValueName {

        /** The same name, carried into a reader by {@code module}'s published body. */
        public OfType publishedBy(String module) {
            return new OfType(name, type, module);
        }

        @Override
        public String toString() {
            return type.toString();
        }
    }

    /** A name the language itself gives a meaning: {@code None}, and the rounding modes a
     * {@code divide} takes. Declared by no module and bound by no body. */
    record Builtin(String name) implements ValueName {

        @Override
        public String toString() {
            return name;
        }
    }

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
