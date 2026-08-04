package souther.compiler.types;

/**
 * The Souther value types. Either a primitive ({@code Int}/{@code String}/{@code Bool})
 * or a reference to a named data type. {@code Type.INT} etc. remain usable as constants.
 */
public sealed interface Type
        permits Type.Prim, Type.Ref, Type.ListOf, Type.MapOf, Type.SetOf, Type.OptionOf, Type.Union,
                Type.FnOf, Type.Open, Type.Nothing, Type.Never, Type.TupleOf, Type.Erroneous {

    /**
     * A type that stands for another rather than being one. There are two, and they differ in who
     * gets to say what it stands for: a {@link Var} is a declaration's, and every use of that
     * declaration must hold for it; a {@link MetaVar} is one application's, and that application
     * decides it. Wherever the question is only "does this stand for something else", both answer
     * yes, and a reader asking it says so by naming this.
     */
    sealed interface Open extends Type permits Var, MetaVar {}

    enum Prim implements Type { INT, STRING, BOOL, DECIMAL, DATE, DATETIME, RAW }

    /** The element type of the empty-list literal {@code []} (ADR-0028): a bottom that unifies with
     * any element type. It only ever appears as {@code ListOf(NOTHING)} — the empty list — whose type
     * is fixed by context ({@code ++}, an {@code if}/{@code match} case, a {@code fold} seed, or the
     * {@code List<T>} a position expects). It never reaches codegen: an empty list is element-agnostic
     * at runtime. */
    record Nothing() implements Type {}

    /**
     * The type of an expression that answers no value: {@code unreachable "reason"}, and nothing
     * else. It fits every expected type, and joining it with a type yields that type, so an arm
     * that cannot arise leaves the {@code match} typed by the arms that can.
     *
     * <p>It is not {@link Nothing}. That one is an inference result waiting to be filled in — the
     * element of {@code []} — and a pass that meets it asks what the context makes it. This one is
     * an answer: nothing arrives here.
     *
     * <p>Fitting every type is not being one. The code around the abort is still emitted and still
     * reads a shape, so where this survives to codegen — the position stated no type and no branch
     * beside it supplied one — that position is refused rather than emitted.
     */
    record Never() implements Type {}

    /**
     * A type the compiler could not work out, and has already said so about.
     *
     * <p>It exists so that being wrong about one thing does not stop the compiler saying anything
     * about the rest. A name that denotes nothing used to end the module: everything after it went
     * unchecked, and an editor could not answer what any name in the file meant, which is when an
     * author most wants to ask. The name denotes this instead, the tree stays whole, and the passes
     * below carry on.
     *
     * <p>It absorbs. Every comparison with it holds and every join with it yields it, so the one
     * mistake is reported once rather than as a mismatch at each place the value flowed. That is what
     * makes it different from {@link Nothing}, which is a real inference result — the element type of
     * {@code []} — and must not silence anything.
     *
     * <p>It never reaches codegen. There is no bytecode for a type nobody could name, so the one
     * place that gates emitting a module refuses a tree that holds one.
     */
    record Erroneous() implements Type {}

    /**
     * A type variable ({@code 'a}). It stands for any type; a non-recursive helper carrying one is
     * monomorphised by inline expansion, so the variable is resolved to the concrete argument type at
     * each call site.
     *
     * <p>{@code inferred} is whether the compiler made it. A variable the shipped core wrote is not:
     * its spelling is what an author of core reads. One the compiler minted is: it stands for a value
     * a use decides, and its spelling is an internal name that says nothing to anyone, so nothing
     * shows it.
     */
    record Var(String name, boolean inferred) implements Open {}

    /**
     * A variable one application of a signature left open, waiting to be decided by that
     * application. It is not {@link Var}: that one stands for any type and may not be rewritten,
     * because it is what a declaration wrote and every use of the declaration must hold for it.
     * This one stands for the one type a single application settles on, and is rewritten as soon as
     * something says what that is.
     *
     * <p>Identity is the pair, not the spelling. {@code application} is the expansion of one call,
     * and {@code spelling} is the variable that call's callee wrote, which is unique within a
     * signature. So two occurrences of {@code 'a} in one signature are one variable at one call, and
     * two calls of that signature leave two — which is the rule this exists to state.
     *
     * <p>It lives no longer than the elaboration of the expansion that made it. Every one is either
     * decided there or read as {@link Nothing} at its boundary (ADR-0028), so nothing below sees one
     * and no answer the compiler stores holds one.
     */
    record MetaVar(BindingOwner application, String spelling) implements Open {

        public MetaVar {
            if (application == null || spelling == null) {
                throw new IllegalArgumentException(
                        "a meta variable needs an application and a spelling: " + application + " "
                                + spelling);
            }
        }

        @Override
        public String toString() {
            return spelling + "@" + application;
        }
    }

    /** A reference to a named data type (product or sum). */
    record Ref(TypeName name) implements Type {
        public Ref {
            if (name == null) {
                throw new IllegalArgumentException("a type reference needs a resolved name");
            }
        }
    }

    /** A homogeneous list of {@code element}. */
    record ListOf(Type element) implements Type {}

    /** A {@code Map<key, value>}. The key is {@code String} or a String-backed newtype (ADR-0040);
     * at runtime the map is keyed by that value (value equality, ADR-0009) and its external
     * representation is a JSON object whose string keys are the key's bare form. */
    record MapOf(Type key, Type value) implements Type {}

    /** A {@code Set<element>} — an unordered collection with no duplicate elements, compared by value
     * equality (ADR-0009). Its external representation is a JSON array, deduplicated on decode. */
    record SetOf(Type element) implements Type {}

    /** An optional value {@code Option<element>} — the desugaring of a {@code T?} field (spec 7.4). */
    record OptionOf(Type element) implements Type {}

    /** An anonymous union of data types (a behavior's multi-success output). */
    record Union(java.util.Set<TypeName> members) implements Type {}

    /** A function type {@code (params...) -> result}. Written only on a helper {@code fn}'s
     * parameter (spec §fn-declaration); a value of this type is never stored in a data field, so it
     * never crosses a codec boundary. */
    record FnOf(java.util.List<Type> params, Type result) implements Type {}

    /** A tuple {@code (A, B, ...)} of two or more element types (ADR-0036). Expression-level only —
     * like {@link FnOf}, a tuple is never stored in a data field or a behavior's I/O, so it never
     * crosses a codec boundary; it only carries several values through a computation. */
    record TupleOf(java.util.List<Type> elements) implements Type {}

    /** The one {@link Erroneous}: it carries nothing, so there is nothing to tell two apart. */
    Type ERRONEOUS = new Erroneous();

    Type INT = Prim.INT;
    Type STRING = Prim.STRING;
    Type BOOL = Prim.BOOL;
    Type DECIMAL = Prim.DECIMAL;
    Type DATE = Prim.DATE;
    Type DATETIME = Prim.DATETIME;
    /** The external (encoded) representation type: an encoder's raw output at a railway's edge,
     * unioned with propagated error cases as the case {@code "Raw"} (spec 24). Reserved — no stage
     * produces it yet; {@code >->} composes behaviors, not codecs (spec 14.1). */
    Type RAW = Prim.RAW;
    /** The bottom element type of the empty-list literal (see {@link Nothing}). */
    Type NOTHING = new Nothing();
    /** The type of the empty-list literal {@code []}: a list whose element type is not yet fixed. */
    Type EMPTY_LIST = new ListOf(NOTHING);
    /** The type of {@code unreachable "reason"} (see {@link Never}). */
    Type NEVER = new Never();

    static Type ref(TypeName name) {
        return new Ref(name);
    }

    static Type list(Type element) {
        return new ListOf(element);
    }

    static Type option(Type element) {
        return new OptionOf(element);
    }

    /** A string-keyed map (the common case): {@code MapOf(STRING, value)}. */
    static Type map(Type value) {
        return new MapOf(STRING, value);
    }

    /** A map with an explicit key type (a String or a String-backed newtype). */
    static Type map(Type key, Type value) {
        return new MapOf(key, value);
    }

    static Type set(Type element) {
        return new SetOf(element);
    }

    static Type union(java.util.Set<TypeName> members) {
        return new Union(members);
    }

    static Type fn(java.util.List<Type> params, Type result) {
        return new FnOf(params, result);
    }

    static Type tuple(java.util.List<Type> elements) {
        return new TupleOf(elements);
    }

    /** A variable as the core wrote it. */
    static Type var(String name) {
        return new Var(name, false);
    }

    /** A variable the compiler minted, standing for a value each use of the declaration decides. */
    static Type inferredVar(String name) {
        return new Var(name, true);
    }

    /** A user-facing rendering of {@code t} in surface syntax: {@code Int}, {@code List<Int>},
     * {@code A | B}, {@code (A, B)}, {@code T?}. Used by diagnostics; unlike the record {@code toString}
     * it reads the way the source is written. */
    static String show(Type t) {
        return show(t, java.util.Set.<String>of());
    }

    /**
     * Renders {@code t} for a message that also shows {@code against}. Where one name stands for two
     * types — {@code Mid} of one module beside {@code Mid} of another — both are written with their
     * module, so a mismatch does not read as {@code Mid} against {@code Mid}.
     */
    static String show(Type t, Type against) {
        java.util.Map<String, TypeName> here = new java.util.HashMap<>();
        collectNames(t, here);
        java.util.Map<String, TypeName> there = new java.util.HashMap<>();
        collectNames(against, there);
        java.util.Set<String> ambiguous = new java.util.HashSet<>();
        for (java.util.Map.Entry<String, TypeName> e : here.entrySet()) {
            TypeName other = there.get(e.getKey());
            if (other != null && !other.equals(e.getValue())) {
                ambiguous.add(e.getKey());
            }
        }
        return show(t, ambiguous);
    }

    /** Every name {@code t} mentions, by the simple name it would be written under. A simple name
     * that covers two different types in one type is already ambiguous within it, and is recorded
     * under whichever came first — the pair rendering only has to tell the two sides apart. */
    private static void collectNames(Type t, java.util.Map<String, TypeName> out) {
        switch (t) {
            case Ref r -> out.putIfAbsent(r.name().name(), r.name());
            case Union u -> u.members().forEach(m -> out.putIfAbsent(m.name(), m));
            case ListOf l -> collectNames(l.element(), out);
            case SetOf s -> collectNames(s.element(), out);
            case OptionOf o -> collectNames(o.element(), out);
            case MapOf m -> {
                collectNames(m.key(), out);
                collectNames(m.value(), out);
            }
            case TupleOf tu -> tu.elements().forEach(e -> collectNames(e, out));
            case FnOf f -> {
                f.params().forEach(p -> collectNames(p, out));
                collectNames(f.result(), out);
            }
            case Prim _, Var _, MetaVar _, Nothing _, Never _, Erroneous _ -> { }
        }
    }

    /**
     * {@code t} with every name written with its module. This is the form a signature takes when it
     * is published for another project to read: nothing is known there about what the reading module
     * imports, so no name is left to be resolved by whatever happens to be in scope.
     */
    static String showQualified(Type t) {
        java.util.Map<String, TypeName> names = new java.util.HashMap<>();
        collectNames(t, names);
        return show(t, names.keySet());
    }

    /** {@code name}, written with its module when the simple name is one of {@code qualify}. */
    private static String showName(TypeName name, java.util.Set<String> qualify) {
        return qualify.contains(name.name()) ? name.qualified() : name.name();
    }

    private static String show(Type t, java.util.Set<String> qualify) {
        return switch (t) {
            case Prim p -> switch (p) {
                case INT -> "Int";
                case STRING -> "String";
                case BOOL -> "Bool";
                case DECIMAL -> "Decimal";
                case DATE -> "Date";
                case DATETIME -> "DateTime";
                case RAW -> "Raw";
            };
            case Ref r -> showName(r.name(), qualify);
            // A variable the core wrote is shown as the core wrote it; the name carries the `'`
            // (`'a`), so it is not added twice. One the compiler minted is shown as `_`: its spelling
            // is an internal name an author never wrote and could not write, so it says nothing to
            // the reader, while what is open about the type is what they need.
            case Var v -> v.inferred() ? "_"
                    : v.name().startsWith("'") ? v.name() : "'" + v.name();
            // What an application has not decided yet. Shown as what is open about the type, like
            // every other variable the author did not write: the call it belongs to says nothing to
            // someone reading their own program.
            case MetaVar _ -> "_";
            case Nothing _ -> "_";
            case Never _ -> "Never";
            // An error type should not reach a message: it absorbs, so nothing compares against it
            // and finds a mismatch to describe. If one does, say what it is rather than a shape the
            // author could go looking for.
            case Erroneous _ -> "?";
            case ListOf l -> "List<" + show(l.element(), qualify) + ">";
            case SetOf s -> "Set<" + show(s.element(), qualify) + ">";
            case OptionOf o -> show(o.element(), qualify) + "?";
            case MapOf m -> "Map<" + show(m.key(), qualify) + ", " + show(m.value(), qualify) + ">";
            case Union u -> u.members().stream().map(n -> showName(n, qualify))
                    .collect(java.util.stream.Collectors.joining(" | "));
            case TupleOf tu -> tu.elements().stream().map(e -> show(e, qualify))
                    .collect(java.util.stream.Collectors.joining(", ", "(", ")"));
            case FnOf f -> f.params().stream().map(p -> show(p, qualify))
                    .collect(java.util.stream.Collectors.joining(", ", "(", ")"))
                    + " -> " + show(f.result(), qualify);
        };
    }

    /** Whether {@code t}, or any type nested inside it, satisfies {@code p}. Tests {@code t} itself
     * first, then recurses through every position that holds a type: a collection's element,
     * a {@code Map}'s key and value, a {@code Tuple}'s members, a function type's parameters and
     * result. A {@code Union} ends the walk: its members are names, not nested types. The single
     * tree walk both "contains a tuple" and "still carries the empty-collection bottom" are
     * expressed over. */
    static boolean mentions(Type t, java.util.function.Predicate<Type> p) {
        if (p.test(t)) {
            return true;
        }
        return switch (t) {
            case ListOf l -> mentions(l.element(), p);
            case SetOf s -> mentions(s.element(), p);
            case OptionOf o -> mentions(o.element(), p);
            case MapOf m -> mentions(m.key(), p) || mentions(m.value(), p);
            case TupleOf tu -> tu.elements().stream().anyMatch(e -> mentions(e, p));
            case FnOf f -> f.params().stream().anyMatch(a -> mentions(a, p))
                    || mentions(f.result(), p);
            case Prim _, Ref _, Var _, MetaVar _, Nothing _, Never _, Erroneous _, Union _ -> false;
        };
    }
}
