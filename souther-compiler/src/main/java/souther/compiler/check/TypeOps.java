package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.SourcePos;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The type-level questions the checker asks, independent of any expression being checked: resolving
 * a written type, deciding assignability, unifying an intrinsic's type variables, and reading what a
 * data or a newtype is made of.
 *
 * <p>Every operation here is a pure function of a type and the module's symbol table, so it is
 * static and can be called from the backend as well as from the checker.
 */
public final class TypeOps {

    private TypeOps() {}

    /** Resolves a helper parameter's written type: an ordinary type or a function type. */
    public static Type resolveParamType(Ast.ParamType t, Symbols symbols) {
        return switch (t) {
            case Ast.RetType rt -> successType(rt, symbols);
            case Ast.FnType ft -> {
                List<Type> params = new ArrayList<>();
                for (Ast.RetType p : ft.params()) {
                    params.add(successType(p, symbols));
                }
                yield Type.fn(params, successType(ft.result(), symbols));
            }
        };
    }

    /** The output type of a behavior return: a single case, or a union of two or more cases. */
    public static Type successType(Ast.RetType ret, Symbols symbols) {
        List<Type> members = new ArrayList<>();
        for (Ast.TypeRef t : ret.cases()) {
            members.add(resolveType(t, symbols));
        }
        if (members.size() == 1) {
            return members.get(0);
        }
        Set<TypeName> names = new HashSet<>();
        for (Type m : members) {
            if (!(m instanceof Type.Ref r)) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.union.members").title("check.boundary.title")
                                .at(ret.pos()).build(),
                        "union members must be data types");
            }
            names.add(r.name());
        }
        return Type.union(names);
    }

    /** Builds a Ref (one name) or Union (two or more) from a set of case names. */
    static Type caseSetType(Set<TypeName> names) {
        if (names.size() == 1) {
            return Type.ref(names.iterator().next());
        }
        return Type.union(names);
    }

    public static boolean isDataLike(Type t) {
        return t instanceof Type.Ref || t instanceof Type.Union;
    }

    public static Set<TypeName> namesOf(Type t) {
        if (t instanceof Type.Ref r) {
            return Set.of(r.name());
        }
        if (t instanceof Type.Union u) {
            return u.members();
        }
        return Set.of();
    }

    /** Case names of a stage output, treating a {@code Raw} encoder output as the case {@code "Raw"}
     * so it can be unioned with propagated error cases (spec 14.1, 24). */
    static Set<TypeName> caseNamesOf(Type t) {
        if (t == Type.RAW) {
            return Set.of(TypeName.primitive("Raw"));
        }
        return namesOf(t);
    }

    /** True when a value of {@code sub} is acceptable where {@code sup} is expected. */
    public static boolean subtypeOf(Type sub, Type sup) {
        if (sub.equals(sup)) {
            return true;
        }
        return sup instanceof Type.Union u && u.members().containsAll(namesOf(sub));
    }

    /** The sum type that {@code t}'s case belongs to, or null when {@code t} is not a case of a named
     * sum. A {@code fold} whose seed is a case ({@code PricedCart}) and whose step grows and matches the
     * accumulator at the sum ({@code PricedCart | NotFound}) is typed at that sum, not the seed case. */
    public static Type enclosingSum(Type t, Symbols symbols) {
        if (!(t instanceof Type.Ref ref) || symbols.get(ref.name()) instanceof Ast.SumData) {
            return null;
        }
        // A sum and its cases are declared together, so only that module can hold the sum this case
        // belongs to. A case may belong to more than one; pick by name so the choice is deterministic
        // across runs rather than dependent on the symbol map's iteration order.
        String chosen = null;
        for (Ast.Def d : symbols.declaredIn(ref.name().module()).values()) {
            if (d instanceof Ast.SumData sum && sum.cases().contains(ref.name().name())
                    && (chosen == null || sum.name().compareTo(chosen) < 0)) {
                chosen = sum.name();
            }
        }
        return chosen == null ? null : Type.ref(ref.name().sibling(chosen));
    }

    public static boolean isSumType(Type t, Symbols symbols) {
        return t instanceof Type.Union
                || (t instanceof Type.Ref r && symbols.get(r.name()) instanceof Ast.SumData);
    }

    /** The cases of {@code t} when it is a sum — a declared {@code data S = A | B} or the union a
     * branch widened to — with a case that is itself a sum folded to its own cases. Null when
     * {@code t} is not a sum at all. */
    static List<TypeName> sumCases(Type t, Symbols symbols) {
        return sumCases(t, symbols, new HashSet<>());
    }

    private static List<TypeName> sumCases(Type t, Symbols symbols, Set<TypeName> visiting) {
        List<TypeName> names;
        if (t instanceof Type.Ref ref && symbols.get(ref.name()) instanceof Ast.SumData sum) {
            if (!visiting.add(ref.name())) {
                return List.of();   // a sum reaching itself; DataChecker reports it, this must terminate
            }
            names = caseNames(ref.name(), sum);
        } else if (t instanceof Type.Union union) {
            names = List.copyOf(union.members());
        } else {
            return null;
        }
        List<TypeName> leaves = new ArrayList<>();
        for (TypeName name : names) {
            List<TypeName> nested = symbols.get(name) instanceof Ast.SumData
                    ? sumCases(Type.ref(name), symbols, visiting) : null;
            if (nested == null) {
                leaves.add(name);
            } else {
                leaves.addAll(nested);
            }
        }
        return leaves;
    }

    /** A sum's cases, canonical. A case is declared in the same module as the sum that lists it — the
     * generated sum is a sealed interface, which only its own package can implement — so the sum's
     * module is the case's. */
    public static List<TypeName> caseNames(TypeName sumName, Ast.SumData sum) {
        List<TypeName> names = new ArrayList<>();
        for (String c : sum.cases()) {
            names.add(sumName.sibling(c));
        }
        return names;
    }

    /** Whether a {@code from} value can be assigned where {@code to} is expected. Lists are
     * covariant, and a data-like type widens to the set of leaf cases it can be — so a list of
     * a sum's cases is assignable to a list of the sum (spec 8.3, 12.2). */
    public static boolean assignable(Type from, Type to, Symbols symbols) {
        if (from.equals(to)) {
            return true;
        }
        if (from == Type.NOTHING) {
            return true;   // the empty list's bottom element assigns into any element type (ADR-0028)
        }
        // immutable collections are element-covariant: A <: S makes a List/Map/Option of A
        // assignable to one of S. Sound because they cannot be mutated (spec 6), so no write can
        // smuggle a sibling case in — the same reason Scala's immutable List and Kotlin's read-only
        // List are covariant, and Java's mutable arrays are not.
        if (from instanceof Type.ListOf a && to instanceof Type.ListOf b) {
            return assignable(a.element(), b.element(), symbols);
        }
        if (from instanceof Type.MapOf a && to instanceof Type.MapOf b) {
            return assignable(a.key(), b.key(), symbols) && assignable(a.value(), b.value(), symbols);
        }
        if (from instanceof Type.SetOf a && to instanceof Type.SetOf b) {
            return assignable(a.element(), b.element(), symbols);
        }
        if (from instanceof Type.OptionOf a && to instanceof Type.OptionOf b) {
            return assignable(a.element(), b.element(), symbols);
        }
        if (from instanceof Type.TupleOf a && to instanceof Type.TupleOf b
                && a.elements().size() == b.elements().size()) {
            for (int i = 0; i < a.elements().size(); i++) {
                if (!assignable(a.elements().get(i), b.elements().get(i), symbols)) {
                    return false;
                }
            }
            return true;
        }
        Set<TypeName> fa = leafCases(from, symbols);
        Set<TypeName> ta = leafCases(to, symbols);
        return !fa.isEmpty() && !ta.isEmpty() && ta.containsAll(fa);
    }

    /** The type two joined positions ({@code if} branches, {@code match} arms) agree on, or
     * {@code null} when they agree on none and the caller reports the disagreement.
     *
     * <p>It descends the covariant constructors {@link #assignable} descends, so the widening a leaf
     * gets applies under one too: two data-like types widen to the union of their cases, and a list
     * of one case joins a list of another as a list of both — the same direction {@code ++} takes
     * on its elements (spec 12.2, 16.2). An empty collection's bottom takes on the other side's
     * type, at the top or at any depth, so a bare {@code Set.empty()} accumulator joins the
     * {@code Set<Int>} the other arm grows and a {@code (Set.empty(), [])} joins position by
     * position. */
    public static Type join(Type a, Type b) {
        if (a.equals(b)) {
            return a;
        }
        if (BottomInfer.isBottom(a)) {
            return b;
        }
        if (BottomInfer.isBottom(b)) {
            return a;
        }
        if (a instanceof Type.ListOf la && b instanceof Type.ListOf lb) {
            Type e = join(la.element(), lb.element());
            return e == null ? null : Type.list(e);
        }
        if (a instanceof Type.SetOf sa && b instanceof Type.SetOf sb) {
            Type e = join(sa.element(), sb.element());
            return e == null ? null : Type.set(e);
        }
        if (a instanceof Type.OptionOf oa && b instanceof Type.OptionOf ob) {
            Type e = join(oa.element(), ob.element());
            return e == null ? null : Type.option(e);
        }
        if (a instanceof Type.MapOf ma && b instanceof Type.MapOf mb) {
            Type k = join(ma.key(), mb.key());
            Type v = join(ma.value(), mb.value());
            return k == null || v == null ? null : Type.map(k, v);
        }
        if (a instanceof Type.TupleOf ta && b instanceof Type.TupleOf tb
                && ta.elements().size() == tb.elements().size()) {
            List<Type> elements = new ArrayList<>();
            for (int i = 0; i < ta.elements().size(); i++) {
                Type e = join(ta.elements().get(i), tb.elements().get(i));
                if (e == null) {
                    return null;
                }
                elements.add(e);
            }
            return Type.tuple(elements);
        }
        if (isDataLike(a) && isDataLike(b)) {
            Set<TypeName> names = new HashSet<>(namesOf(a));
            names.addAll(namesOf(b));
            return caseSetType(names);
        }
        return null;
    }

    /**
     * Matches an intrinsic's declared parameter type against an actual argument type, binding any
     * type variables it carries (spec §intrinsics). A variable binds on first sight and every later
     * occurrence must agree; a composite ({@code List<'a>}, {@code Map<String, 'a>}) recurses into
     * its element; a concrete parameter just requires the argument to be assignable. This is what
     * monomorphises a generic intrinsic — {@code values(m: Map<String, 'a>): List<'a>} learns
     * {@code 'a} from the map so {@link #substitute} can resolve the {@code List<'a>} result.
     */
    public static void unify(Type param, Type arg, Map<String, Type> bindings,
                             Symbols symbols, SourcePos pos, String what) {
        switch (param) {
            case Type.Var v -> {
                Type bound = bindings.get(v.name());
                if (bound == null || bound == Type.NOTHING) {
                    // first sight, or widen an empty-collection bottom to a concrete element: an
                    // earlier `[]` / `Map.empty` argument bound NOTHING, and a later real element
                    // fixes it (ADR-0028). Order-independent, so insert(k, v, Map.empty) infers V.
                    bindings.put(v.name(), arg);
                } else if (arg == Type.NOTHING) {
                    // the empty bottom absorbs into the concrete binding already learned
                } else if (!assignable(arg, bound, symbols) && !assignable(bound, arg, symbols)) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.generic.arg").title("check.type.mismatch.title")
                                    .at(pos).args(what, Type.show(bound), Type.show(arg))
                                    .diff(Type.show(arg, bound), Type.show(bound, arg)).build(),
                            what + ": expected " + bound + " but got " + arg);
                }
            }
            case Type.ListOf p when arg instanceof Type.ListOf a ->
                    unify(p.element(), a.element(), bindings, symbols, pos, what);
            case Type.MapOf p when arg instanceof Type.MapOf a -> {
                unify(p.key(), a.key(), bindings, symbols, pos, what);
                unify(p.value(), a.value(), bindings, symbols, pos, what);
            }
            case Type.SetOf p when arg instanceof Type.SetOf a ->
                    unify(p.element(), a.element(), bindings, symbols, pos, what);
            case Type.OptionOf p when arg instanceof Type.OptionOf a ->
                    unify(p.element(), a.element(), bindings, symbols, pos, what);
            case Type.TupleOf p when arg instanceof Type.TupleOf a
                    && p.elements().size() == a.elements().size() -> {
                for (int i = 0; i < p.elements().size(); i++) {
                    unify(p.elements().get(i), a.elements().get(i), bindings, symbols, pos, what);
                }
            }
            case Type.FnOf p when arg instanceof Type.FnOf a && p.params().size() == a.params().size() -> {
                for (int i = 0; i < p.params().size(); i++) {
                    unify(p.params().get(i), a.params().get(i), bindings, symbols, pos, what);
                }
                unify(p.result(), a.result(), bindings, symbols, pos, what);
            }
            default -> {
                if (!assignable(arg, param, symbols)) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.generic.arg").title("check.type.mismatch.title")
                                    .at(pos).args(what, Type.show(param), Type.show(arg))
                                    .diff(Type.show(arg, param), Type.show(param, arg)).build(),
                            what + ": expected " + param + " but got " + arg);
                }
            }
        }
    }

    /** Replaces the type variables bound by {@link #unify} in a result type. */
    public static Type substitute(Type t, Map<String, Type> bindings) {
        return switch (t) {
            case Type.Var v -> bindings.getOrDefault(v.name(), v);
            case Type.ListOf l -> Type.list(substitute(l.element(), bindings));
            case Type.MapOf m -> Type.map(substitute(m.key(), bindings), substitute(m.value(), bindings));
            case Type.SetOf s -> Type.set(substitute(s.element(), bindings));
            case Type.OptionOf o -> Type.option(substitute(o.element(), bindings));
            case Type.FnOf f -> {
                List<Type> params = new ArrayList<>();
                for (Type p : f.params()) {
                    params.add(substitute(p, bindings));
                }
                yield Type.fn(params, substitute(f.result(), bindings));
            }
            case Type.TupleOf tup -> {
                List<Type> es = new ArrayList<>();
                for (Type e : tup.elements()) {
                    es.add(substitute(e, bindings));
                }
                yield Type.tuple(es);
            }
            default -> t;
        };
    }

    /** The set of leaf (non-sum) case names a data-like type covers, flattening nested sums. */
    public static Set<TypeName> leafCases(Type t, Symbols symbols) {
        Set<TypeName> out = new LinkedHashSet<>();
        collectLeafCases(t, symbols, out, new HashSet<>());
        return out;
    }

    private static void collectLeafCases(Type t, Symbols symbols, Set<TypeName> out,
                                         Set<TypeName> visiting) {
        for (TypeName name : namesOf(t)) {
            if (symbols.get(name) instanceof Ast.SumData s) {
                if (!visiting.add(name)) {
                    continue;   // a sum reaching itself; DataChecker reports it, this must terminate
                }
                for (TypeName caseName : caseNames(name, s)) {
                    collectLeafCases(Type.ref(caseName), symbols, out, visiting);
                }
            } else {
                out.add(name);
            }
        }
    }

    /** Effective field name → type (included data flattened first, then own fields). */
    public static Map<String, Type> fieldTypes(Ast.Data data, Symbols symbols) {
        String home = symbols.moduleOf(data);
        Map<String, Type> types = new LinkedHashMap<>();
        for (String inc : data.includes()) {
            if (!(symbols.get(symbols.resolveIn(home, inc)) instanceof Ast.Data id)) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.spread.notproduct").title("check.construct.title")
                                .at(data.pos()).args(inc).build(),
                        "cannot spread `..." + inc + "` (not a product data)");
            }
            for (Map.Entry<String, Type> e : fieldTypes(id, symbols).entrySet()) {
                if (types.put(e.getKey(), e.getValue()) != null) {
                    throw CompileException.of(
                            Diagnostic.of("E1004", "e1004.msg").at(data.pos())
                                    .args(e.getKey(), inc, data.name()).build(),
                            "Field `" + e.getKey() + "` from `..." + inc + "` conflicts with a field of `"
                                    + data.name() + "`.");
                }
            }
        }
        for (Ast.Field f : data.fields()) {
            if (types.put(f.name(), resolveTypeIn(home, f.type(), symbols)) != null) {
                throw CompileException.of(
                        Diagnostic.of("E1004", "e1004.dup").at(f.pos())
                                .args(f.name(), data.name()).build(),
                        "duplicate field `" + f.name() + "` in `" + data.name() + "`");
            }
        }
        return types;
    }

    /**
     * The resolved type of one field, or null when the data has no such field. Reading a field is not
     * a reason to resolve the data's other fields: a module that imports a data to read one `Int` out
     * of it would otherwise need every sibling field's type in scope, and the failure would carry the
     * declaring module's position (issue #110). The duplicate-field checks {@link #fieldTypes} makes
     * belong to the declaring module's own check, which has already run.
     */
    public static Type fieldType(Ast.Data data, String field, Symbols symbols) {
        String home = symbols.moduleOf(data);
        for (Ast.Field f : data.fields()) {
            if (f.name().equals(field)) {
                return resolveTypeIn(home, f.type(), symbols);
            }
        }
        for (String inc : data.includes()) {
            if (symbols.get(symbols.resolveIn(home, inc)) instanceof Ast.Data included) {
                Type t = fieldType(included, field, symbols);
                if (t != null) {
                    return t;
                }
            }
        }
        return null;
    }

    /** Whether a data has a field of that name, without resolving any type. */
    public static boolean hasField(Ast.Data data, String field, Symbols symbols) {
        for (Ast.Field f : data.fields()) {
            if (f.name().equals(field)) {
                return true;
            }
        }
        for (String inc : data.includes()) {
            if (symbols.get(symbols.resolveIn(symbols.moduleOf(data), inc)) instanceof Ast.Data included
                    && hasField(included, field, symbols)) {
                return true;
            }
        }
        return false;
    }

    /** All invariants that apply to a data: included data's invariants first, then its own. */
    public static List<Ast.Expr> effectiveInvariants(Ast.Data data, Symbols symbols) {
        List<Ast.Expr> invs = new ArrayList<>();
        for (String inc : data.includes()) {
            if (symbols.get(symbols.resolveIn(symbols.moduleOf(data), inc)) instanceof Ast.Data id) {
                invs.addAll(effectiveInvariants(id, symbols));
            }
        }
        data.invariant().ifPresent(invs::add);
        return invs;
    }

    /** The type a newtype wraps ({@code data X = Y} gives {@code Y}), or null when {@code name} is not
     * a newtype — the implicit inner field is {@code value}. */
    static Type newtypeInner(TypeName name, Symbols symbols) {
        if (symbols.get(name) instanceof Ast.Data d && d.newtype()) {
            return fieldTypes(d, symbols).get("value");
        }
        return null;
    }

    /** Whether {@code name} is a newtype over {@code String} ({@code data X = String}) — the only key
     *  type a {@code Map} admits besides {@code String} itself (ADR-0040). */
    static boolean isStringNewtype(TypeName name, Symbols symbols) {
        return symbols.get(name) instanceof Ast.Data d && d.newtype()
                && d.fields().size() == 1 && "String".equals(d.fields().get(0).type().name());
    }

    /**
     * Whether {@code key} can key a {@code Map} that crosses the boundary. A map's external form is a
     * JSON object, whose keys are strings, so the key type must render as and parse from a bare
     * string: {@code String}, a String-backed newtype (ADR-0040), or a temporal — a {@code Date}
     * field already travels as its ISO form, so an ISO key is the same representation in key
     * position. A key type variable is admitted for the {@code core} signatures, which monomorphise
     * to one of those.
     */
    public static boolean isBoundaryMapKey(Type key, Symbols symbols) {
        return key == Type.STRING || key == Type.DATE || key == Type.DATETIME
                || key instanceof Type.Var
                || (key instanceof Type.Ref r && isStringNewtype(r.name(), symbols));
    }

    /** The key of the first {@code Map} inside {@code t} that cannot cross the boundary, or null when
     * every one can — what a data field or a behavior's input/output is checked against. */
    public static Type nonBoundaryMapKey(Type t, Symbols symbols) {
        if (t instanceof Type.MapOf m && !isBoundaryMapKey(m.key(), symbols)) {
            return m.key();
        }
        return switch (t) {
            case Type.ListOf l -> nonBoundaryMapKey(l.element(), symbols);
            case Type.SetOf s -> nonBoundaryMapKey(s.element(), symbols);
            case Type.OptionOf o -> nonBoundaryMapKey(o.element(), symbols);
            case Type.MapOf m -> nonBoundaryMapKey(m.value(), symbols);
            case Type.TupleOf tu -> tu.elements().stream()
                    .map(e -> nonBoundaryMapKey(e, symbols)).filter(k -> k != null).findFirst().orElse(null);
            default -> null;
        };
    }

    static boolean isSingleValueNewtype(Type t, Symbols symbols) {
        return t instanceof Type.Ref ref
                && symbols.get(ref.name()) instanceof Ast.Data d && d.newtype();
    }

    /** The ordered primitives: the ones the JVM carries as {@link Comparable}, so {@code <}/{@code >}
     * and {@code sort} work on them (spec §primitives, §stdlib-list). */
    static boolean isOrdered(Type t) {
        return t == Type.INT || t == Type.STRING || t == Type.DECIMAL
                || t == Type.DATE || t == Type.DATETIME;
    }

    /** Whether a value of {@code t} is ordered: an ordered primitive, or a single-value newtype over
     * one — it is ordered by the value it wraps (ADR-0047), which is what both the comparison
     * operators and the sort family read. The generated wrapper carries that ordering as
     * {@link Comparable}, so the runtime's natural-order compare reaches it. */
    public static boolean isOrderedValue(Type t, Symbols symbols) {
        return isOrdered(base(t, symbols));
    }

    /** The underlying base of a type: itself, or — for a single-value newtype ({@code data X = Y}) —
     * the base of its {@code value} type, recursively (so {@code 管理職 = レベル = Int} bases to Int).
     * A newtype's value is what its comparison and equality read. */
    static Type base(Type t, Symbols symbols) {
        if (isSingleValueNewtype(t, symbols)) {
            Type inner = fieldTypes((Ast.Data) symbols.get(((Type.Ref) t).name()), symbols).get("value");
            if (inner != null) {
                return base(inner, symbols);
            }
        }
        return t;
    }

    /** The Int or Decimal that a single-value newtype directly wraps (one level), or {@code null}
     * (a non-newtype, or a newtype over a non-numeric or over another newtype). */
    static Type directNumericNewtypeBase(Type t, Symbols symbols) {
        if (isSingleValueNewtype(t, symbols)) {
            Type inner = fieldTypes((Ast.Data) symbols.get(((Type.Ref) t).name()), symbols).get("value");
            if (inner == Type.INT || inner == Type.DECIMAL) {
                return inner;
            }
        }
        return null;
    }

    /** The single-value numeric newtype a closed {@code +}/{@code -} over {@code lt} and {@code rt}
     * yields — whichever operand is such a newtype — or {@code null} if neither is. Callers that have
     * already passed the type checker's admissibility gate (codegen, the invariant analysis) use this
     * to pick the result without re-deriving the rule. */
    public static Type closedNewtypeArithResult(Type lt, Type rt, Symbols symbols) {
        if (directNumericNewtypeBase(lt, symbols) != null) {
            return lt;
        }
        if (directNumericNewtypeBase(rt, symbols) != null) {
            return rt;
        }
        return null;
    }

    public static Type primType(Ast.RawKind kind) {
        return switch (kind) {
            case TEXT -> Type.STRING;
            case INT -> Type.INT;
            case BOOL -> Type.BOOL;
            case DECIMAL -> Type.DECIMAL;
            case DATE -> Type.DATE;
            case DATETIME -> Type.DATETIME;
        };
    }

    public static Type primType(Ast.PrimKind kind) {
        return switch (kind) {
            case STRING -> Type.STRING;
            case INT -> Type.INT;
            case BOOL -> Type.BOOL;
            case DECIMAL -> Type.DECIMAL;
            case DATE -> Type.DATE;
            case DATETIME -> Type.DATETIME;
        };
    }

    public static Type resolveType(Ast.TypeRef ref, Symbols symbols) {
        return resolveTypeIn(symbols.module(), ref, symbols);
    }

    /** Resolves a type written inside {@code inModule} — which is the module being compiled for
     * everything it declares itself, and the declaring module for a type read out of an imported
     * data (spec 4). */
    public static Type resolveTypeIn(String inModule, Ast.TypeRef ref, Symbols symbols) {
        if (ref.isTuple()) {
            List<Type> elems = new ArrayList<>();
            for (Ast.TypeRef e : ref.tupleElems()) {
                elems.add(resolveTypeIn(inModule, e, symbols));
            }
            return Type.tuple(elems);   // (A, B, ...) — a helper/stdlib signature only (ADR-0036)
        }
        return switch (ref.name()) {
            case "Int" -> Type.INT;
            case "String" -> Type.STRING;
            case "Bool" -> Type.BOOL;
            case "Decimal" -> Type.DECIMAL;
            case "Date" -> Type.DATE;
            case "DateTime" -> Type.DATETIME;
            // 制約違反 is no longer a writable case: an invariant violation aborts (spec 7.3, 9.4).
            case "List" -> {
                if (ref.arg() == null) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.typearg.list").title("check.typearg.title")
                                    .at(ref.pos(), 4).build(),
                            "List needs a type argument, e.g. List<Int>");
                }
                yield Type.list(resolveTypeIn(inModule, ref.arg(), symbols));
            }
            case "Set" -> {
                if (ref.arg() == null) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.typearg.set").title("check.typearg.title")
                                    .at(ref.pos(), 3).build(),
                            "Set needs a type argument, e.g. Set<String>");
                }
                yield Type.set(resolveTypeIn(inModule, ref.arg(), symbols));
            }
            case "Option" -> {
                if (ref.arg() == null) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.typearg.option").title("check.typearg.title")
                                    .at(ref.pos(), 6).build(),
                            "Option needs a type argument");
                }
                yield Type.option(resolveTypeIn(inModule, ref.arg(), symbols));
            }
            case "Map" -> {
                if (ref.arg() == null) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.typearg.map").title("check.typearg.title")
                                    .at(ref.pos(), 3).build(),
                            "Map needs a value type, e.g. Map<String, Int>");
                }
                // The key is not restricted here: a map that stays inside a behavior body renders
                // nothing, so it may be keyed by any value (`List.groupBy` already builds such maps).
                // What a key must satisfy is the boundary — see #isBoundaryMapKey, checked where a
                // type is a data field or a behavior's input/output.
                Type key = ref.tupleElems() == null
                        ? Type.STRING : resolveTypeIn(inModule, ref.tupleElems().get(0), symbols);
                yield Type.map(key, resolveTypeIn(inModule, ref.arg(), symbols));
            }
            default -> {
                if (ref.name().startsWith("'")) {
                    yield Type.var(ref.name());   // a type variable, admitted only in the core
                }
                TypeName resolved = symbols.resolveIn(inModule, ref.name());
                if (resolved != null) {
                    yield Type.ref(resolved);
                }
                throw unknownType(ref, symbols);
            }
        };
    }

    /**
     * A written type name nothing here denotes. A qualified name says which of three things went
     * wrong, since the qualifier narrows it: the qualifier names no module, the module declares no
     * such type, or it declares it and does not expose it.
     */
    private static CompileException unknownType(Ast.TypeRef ref, Symbols symbols) {
        String written = ref.name();
        int dot = written.lastIndexOf('.');
        if (dot >= 0) {
            String qualifier = written.substring(0, dot);
            String name = written.substring(dot + 1);
            String module = symbols.moduleOfQualifier(qualifier);
            if (module == null) {
                return CompileException.of(
                        Diagnostic.of(null, "check.qualified.unknownmodule").title("check.module.title")
                                .at(ref.pos(), written.length()).args(qualifier, name)
                                .suggestion(Suggest.candidate(qualifier, symbols.qualifiers()))
                                .build(),
                        "no module named `" + qualifier + "`");
            }
            String key = symbols.contains(new TypeName(module, name))
                    ? "check.qualified.notexposed" : "check.qualified.notdefined";
            return CompileException.of(
                    Diagnostic.of(null, key).title("check.module.title")
                            .at(ref.pos(), written.length()).args(name, module)
                            .suggestion(Suggest.candidate(name, symbols.declaredIn(module).keySet()))
                            .build(),
                    "`" + name + "` is not " + (key.endsWith("notexposed") ? "exposed by" : "defined in")
                            + " `" + module + "`");
        }
        Set<String> known = symbols.namesInScope();
        return CompileException.of(
                Diagnostic.of(null, "check.unknown.type.msg")
                        .title("check.unknown.title")
                        .at(ref.pos(), written.length())
                        .args(written)
                        .suggestion(Suggest.candidate(written, known))
                        .build(),
                "unknown type `" + written + "`" + Suggest.hint(written, known));
    }
}
