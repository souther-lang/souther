package souther.compiler.types;

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
     * block's parameter. {@code id} is the binding it was answered with, which is what tells two
     * bindings of one spelling apart; {@code name} is only how it was written.
     */
    record Local(String name, BindingId id) implements ValueName {

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
     * A standard-library function: the alias the library publishes it under ({@code List}) and the
     * operation that alias reaches ({@code map}). A prelude helper, a prelude intrinsic and a checker
     * built-in are one thing to a name: what is on the other side of the name is the library's own
     * business.
     *
     * <p>The alias is not the module that declares the operation and cannot be made into one:
     * {@code souther.list} declares {@code foldFrom}, and a reader reaches it as
     * {@code List.foldFrom}. Both parts are held here so that a reader wanting one of them takes it
     * rather than splitting {@link #qualified()} back apart — a name written by joining two values is
     * a name somebody downstream will try to read them back out of.
     */
    record Stdlib(String alias, String name) implements ValueName {

        public Stdlib {
            if (alias == null) {
                throw new IllegalArgumentException("a library name is reached under an alias");
            }
        }

        /**
         * The namespace itself, applied: {@code Date("2026-09-30")} constructs from the module the
         * alias names, and there is no operation for it to name.
         *
         * <p>The second shape a library name has, and the reason the operation may be absent. Which
         * of the two this is, {@link #isNamespace()} says — not the spelling: an operation a library
         * gave its own module's name would render the same either way, and telling them apart by
         * comparing renderings is the reading-a-name-back-out this type exists to stop.
         */
        public static Stdlib namespace(String alias) {
            return new Stdlib(alias, null);
        }

        /** An operation of the library module published as {@code alias}. */
        public static Stdlib operation(String alias, String name) {
            if (name == null) {
                throw new IllegalArgumentException("an operation has a name: " + alias);
            }
            return new Stdlib(alias, name);
        }

        /** Whether this is the namespace applied rather than an operation of it. */
        public boolean isNamespace() {
            return name == null;
        }

        /** The operation this reaches, or null where it is the namespace itself. */
        public String operation() {
            return name;
        }

        /** What is reached: the operation, or the namespace where the alias was applied itself.
         * Two shapes can answer one string, so a caller asking which shape it is asks
         * {@link #isNamespace()}. */
        @Override
        public String name() {
            return name == null ? alias : name;
        }

        /** The name the library is keyed by, and the one a reader reaches it under. */
        public String qualified() {
            return name == null ? alias : alias + "." + name;
        }

        @Override
        public String toString() {
            return qualified();
        }
    }

    /**
     * A type written where a value goes: a unit data as a value, or a newtype applied to the value
     * it wraps. Which of the two is decided by what the type is, not by how the name was written.
     *
     * <p>{@code origin} says where the construction came from. A unit data is *constructed* by being
     * named, and a construction says where it came from ({@link souther.compiler.ast.Hir.NewData}) so
     * that the permission check can tell the reader's own from one it was handed; a unit data has no
     * node of its own to say it on, so the name says it.
     */
    record OfType(String name, TypeName type, ConstructionOrigin origin) implements ValueName {

        /** The same name, carried into a reader by {@code module}'s published body. */
        public OfType publishedBy(String module) {
            return new OfType(name, type, origin.publishedIn(module));
        }

        /** The same name, carried into a body by a value that body named. */
        public OfType carriedByValue() {
            return new OfType(name, type, origin.carriedByValue());
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
}
