package souther.compiler.types;

/**
 * The Souther value types. Either a primitive ({@code Int}/{@code String}/{@code Bool})
 * or a reference to a named data type. {@code Type.INT} etc. remain usable as constants.
 */
public sealed interface Type
        permits Type.Prim, Type.Ref, Type.ListOf, Type.MapOf, Type.SetOf, Type.OptionOf, Type.Union,
                Type.FnOf, Type.Var, Type.Nothing, Type.TupleOf {

    enum Prim implements Type { INT, STRING, BOOL, DECIMAL, DATE, DATETIME, RAW }

    /** The element type of the empty-list literal {@code []} (ADR-0028): a bottom that unifies with
     * any element type. It only ever appears as {@code ListOf(NOTHING)} — the empty list — whose type
     * is fixed by context ({@code ++}, an {@code if}/{@code match} case, a {@code fold} seed, or the
     * {@code List<T>} a position expects). It never reaches codegen: an empty list is element-agnostic
     * at runtime. */
    record Nothing() implements Type {}

    /** A type variable ({@code 'a}), written only in the shipped core (ADR-0028). It stands for any
     * type; a non-recursive core helper carrying one is monomorphised by inline expansion, so the
     * variable is resolved to the concrete argument type at each call site. */
    record Var(String name) implements Type {}

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

    static Type var(String name) {
        return new Var(name);
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
            default -> { }
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
            // the name carries the `'` it was written with (`'a`), so it is not added twice
            case Var v -> v.name().startsWith("'") ? v.name() : "'" + v.name();
            case Nothing _ -> "_";
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
     * first, then recurses through the collection types ({@code List}/{@code Set}/{@code Option}
     * element, {@code Map} key and value, {@code Tuple} members). The single tree walk both
     * "contains a tuple" and "still carries the empty-collection bottom" are expressed over. */
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
            default -> false;
        };
    }
}
