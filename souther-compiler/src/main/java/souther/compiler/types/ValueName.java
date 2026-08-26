package souther.compiler.types;

import souther.compiler.Reserved;

/**
 * What a name written in the value namespace denotes — the answer {@link TypeSymbol} gives for the
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
     * A name a module of some compilation declares.
     *
     * <p>The two of them, said as a type. What is reached under a module's own name is exactly what
     * a module declares, so whoever writes that reference takes one of these and has nothing to
     * refuse — where this was a check, a name the language declares and a binding could be handed
     * over and turned away at run time, and every reader after it had to be told they could not be
     * here.
     *
     * <p>Which module, and under what name. A library operation is not one: {@code souther.list}
     * declares {@code foldFrom} and a reader reaches it under an alias the library publishes, which
     * is a different relation and has {@link ReachName.OfLibrary} for it.
     */
    sealed interface OfAModule extends ValueName permits Helper, Behavior {

        /** The module that declares it. */
        String module();
    }

    /**
     * A name that is not a declaration of anything: a binding in force, a type written where a
     * value goes, a name the language itself gives a meaning.
     *
     * <p>The third of the three worlds a name comes from, said as a type beside the other two. A
     * module declares one ({@link OfAModule}), the library declares one ({@link Stdlib}), or it
     * means what it means where it stands — and only the first two are things a call can be emitted
     * for, which is the division {@link ReachName.Declaration} is over.
     */
    sealed interface InScope extends ValueName permits Local, OfType, Builtin { }

    /**
     * A name bound inside a body: a parameter, a {@code let}, a {@code match} arm's binding, or a
     * block's parameter. {@code id} is the binding it was answered with, which is what tells two
     * bindings of one spelling apart; {@code name} is only how it was written.
     */
    record Local(String name, BindingId id) implements InScope {

        @Override
        public String toString() {
            return name;
        }
    }

    /** A module's own {@code let} — a helper, which is expanded into the body that called it. */
    record Helper(String module, String name) implements OfAModule {

        /** Whether the language declares it rather than a module of some compilation.
         *  @see TypeSymbol#isDeclaredByLanguage() */
        public boolean isDeclaredByLanguage() {
            return Reserved.isNamespace(module);
        }

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
    sealed interface Stdlib extends ValueName permits Stdlib.Operation, Stdlib.Namespace {

        /** The alias the library publishes it under. */
        String alias();

        /**
         * The namespace itself, applied: {@code Date("2026-09-30")} constructs from the module the
         * alias names, and there is no operation for it to name.
         *
         * <p>The second shape a library name has, and the reason it is two records rather than one
         * with an absence in it. Which of the two a name is, the type says — not the spelling: an
         * operation a library gave its own module's name would render the same either way, and
         * telling them apart by comparing renderings is the reading-a-name-back-out this type
         * exists to stop.
         */
        static Namespace namespace(String alias) {
            return new Namespace(alias);
        }

        /** An operation of the library module published as {@code alias}. */
        static Operation operation(String alias, String name) {
            return new Operation(alias, name);
        }

        /** Whether this is the namespace applied rather than an operation of it. A caller that goes
         *  on to use the answer matches on the two instead, which carries it into the type. */
        default boolean isNamespace() {
            return this instanceof Namespace;
        }

        /** An operation the library publishes: the alias it is under, and the operation that alias
         *  reaches. Both parts are held so that a reader wanting one of them takes it rather than
         *  splitting {@link #qualified()} back apart — a name written by joining two values is a
         *  name somebody downstream will try to read them back out of. */
        record Operation(String alias, String name) implements Stdlib {

            public Operation {
                if (alias == null || name == null) {
                    throw new IllegalArgumentException(
                            "an operation is a name under an alias: " + alias + "." + name);
                }
            }

            @Override
            public Type.Prim constructs() {
                return null;   // applying an operation computes; only the namespace builds
            }

            @Override
            public String qualified() {
                return alias + "." + name;
            }

            @Override
            public String toString() {
                return qualified();
            }
        }

        /** The namespace itself, which is a name and reaches no operation of its own. */
        record Namespace(String alias) implements Stdlib {

            public Namespace {
                if (alias == null) {
                    throw new IllegalArgumentException("a library name is reached under an alias");
                }
            }

            /** What is reached is the alias, there being no operation under it here. */
            @Override
            public String name() {
                return alias;
            }

            @Override
            public String qualified() {
                return alias;
            }

            @Override
            public String toString() {
                return alias;
            }
        }

        /**
         * The primitive this builds when it is applied, or null where applying it builds nothing.
         *
         * <p>The one place that says what a library name applied to an argument <em>constructs</em>,
         * as against computing something. Only the namespace itself builds a value —
         * {@code Date("2026-09-30")} — and only where the namespace is one of the temporals;
         * {@code Date.fromParts} is an operation and answers a case, and {@code List} builds nothing
         * by being applied.
         *
         * <p>Asked here rather than at each reader, because a reader that had to answer it took the
         * only thing in reach, which was the spelling in front of the argument. Three of them did,
         * each with a different reading of it, and a model declaring a behavior of its own called
         * {@code Date} was compiled as this construction.
         *
         * <p>What is read is the alias, through {@link Type.Prim#named} — the backwards reading of
         * the one table that writes a primitive out, not a second list of the four spellings. That
         * a namespace constructs the primitive its alias is written as holds because the library
         * publishes it under that alias; a library that published a temporal under some other name
         * would be deciding this here, and this is where it would be decided.
         */
        default Type.Prim constructs() {
            Type.Prim prim = Type.Prim.named(alias());
            return prim != null && prim.temporal() ? prim : null;
        }

        /** The name the library is keyed by, and the one a reader reaches it under. */
        String qualified();
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
    record OfType(String name, TypeSymbol type, ConstructionOrigin origin) implements InScope {

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
    record Builtin(String name) implements InScope {

        @Override
        public String toString() {
            return name;
        }
    }

    /** A behavior, and the module that declares it. */
    record Behavior(String module, String name) implements OfAModule {

        public Behavior {
            if (module == null || name == null) {
                throw new IllegalArgumentException("module and name are required: " + module + "."
                        + name);
            }
        }

        /** Whether the language declares it rather than a module of some compilation.
         *  @see TypeSymbol#isDeclaredByLanguage() */
        public boolean isDeclaredByLanguage() {
            return Reserved.isNamespace(module);
        }

        @Override
        public String toString() {
            return module + "." + name;
        }
    }
}
