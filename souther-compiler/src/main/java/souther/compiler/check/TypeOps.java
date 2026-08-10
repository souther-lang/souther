package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.ast.WrittenName;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.NameMessage;
import souther.compiler.diag.msg.TypeMessage;
import souther.compiler.diag.msg.ModuleMessage;
import souther.compiler.diag.msg.DataMessage;
import souther.compiler.diag.DiagnosticCode;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.BindingId;
import souther.compiler.types.LeafScalar;
import souther.compiler.types.BindingOwner;
import souther.compiler.types.CaseShape;
import souther.compiler.types.MapKeyRepresentation;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

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

    /** Resolves a written type. Kept for the readers that name a parameter's type as such. */
    public static Type resolveParamType(Ast.RetType t, Symbols symbols) {
        return successType(t, symbols);
    }

    /**
     * What a position may require of a type. {@link #EQUALITY} is what {@code ==} requires and what a
     * {@code Set} requires of its element and a {@code Map} of its key; {@link #ORDERING} is what
     * {@code sort} and a {@code sortBy} key require; {@link #EXTERNAL_FORM} is what a data's field, a
     * newtype's base and a behavior's input and output require.
     */
    public enum Requires { EQUALITY, ORDERING, EXTERNAL_FORM }

    /**
     * Whether {@code t} answers {@code required}. One table, so all three answers for a type
     * constructor are read in one place, and neither switch carries a {@code default}: a constructor
     * added to {@link Type}, or a fourth question added here, stops compiling until it is answered —
     * which is where "can the representation actually do this?" gets asked.
     *
     * <p>The three are separate questions, and the arms combine their children differently. Equality
     * and the external form descend into what a collection holds. An ordering does not: a collection
     * has none of its own whatever it holds.
     *
     * <p>They are also asked at different times, which is why the question is a parameter rather than
     * three fields computed together. Equality and the external form are answered by the shape of the
     * type alone; only an ordering consults the module, to learn what a {@code Ref} denotes. A
     * {@code Set}'s element is asked for equality while its own type is still being resolved, and
     * there is no answer about ordering to be had yet.
     *
     * <p>{@code Raw} answers yes to equality because its value's own {@code equals} answers, and that
     * is the only answer available: a Raw is an arbitrary Java object and the language promises
     * nothing about it. It is the one place a capability is claimed that the representation does not
     * guarantee.
     *
     * <p>A variable, {@code Nothing}, {@code Never} and {@code Erroneous} stand for a type rather
     * than being one. They answer the way an unconstrained type does, so a generic core signature and
     * a module that already reported an error are not refused a second time for what they hold.
     */
    public static boolean answers(Type t, Requires required, Symbols symbols) {
        return switch (t) {
            case Type.Prim p -> switch (required) {
                case EQUALITY, EXTERNAL_FORM -> true;
                case ORDERING -> isOrdered(p);
            };
            case Type.Ref r -> switch (required) {
                case EQUALITY, EXTERNAL_FORM -> true;
                case ORDERING -> isOrdered(base(r, symbols)) || orderingEnumeration(r, symbols) != null;
            };
            case Type.Union u -> switch (required) {
                case EQUALITY, EXTERNAL_FORM -> true;
                case ORDERING -> orderingEnumeration(u, symbols) != null;
            };
            case Type.ListOf l -> switch (required) {
                case EQUALITY, EXTERNAL_FORM -> answers(l.element(), required, symbols);
                case ORDERING -> false;
            };
            case Type.SetOf s -> switch (required) {
                case EQUALITY, EXTERNAL_FORM -> answers(s.element(), required, symbols);
                case ORDERING -> false;
            };
            case Type.OptionOf o -> switch (required) {
                case EQUALITY, EXTERNAL_FORM -> answers(o.element(), required, symbols);
                case ORDERING -> false;
            };
            case Type.MapOf m -> switch (required) {
                case EQUALITY, EXTERNAL_FORM -> answers(m.key(), required, symbols)
                        && answers(m.value(), required, symbols);
                case ORDERING -> false;
            };
            case Type.TupleOf tu -> switch (required) {
                case EQUALITY -> {
                    for (Type e : tu.elements()) {
                        if (!answers(e, required, symbols)) {
                            yield false;
                        }
                    }
                    yield true;
                }
                // a tuple carries values through a computation and is never encoded, whatever it holds
                case ORDERING, EXTERNAL_FORM -> false;
            };
            case Type.FnOf _ -> false;
            case Type.Open _, Type.Nothing _, Type.Never _, Type.Erroneous _ -> switch (required) {
                case EQUALITY, EXTERNAL_FORM -> true;
                case ORDERING -> false;
            };
        };
    }

    /**
     * Whether values of this type can be compared for equality — what {@code ==} requires, and what
     * a {@code Set} requires of its element and a {@code Map} of its key (ADR-0009, ADR-0039).
     */
    public static boolean supportsEquality(Type t, Symbols symbols) {
        return answers(t, Requires.EQUALITY, symbols);
    }

    /** Whether values of this type have an ordering — what {@code sort} and a {@code sortBy} key
     * require of what they order. A single-value newtype is ordered by the value it wraps
     * (ADR-0047), and an enumeration by the order its cases are declared in. */
    public static boolean supportsOrdering(Type t, Symbols symbols) {
        return answers(t, Requires.ORDERING, symbols);
    }

    /**
     * Whether a value of this type has an external representation — what a boundary requires of it
     * (ADR-0004). A boundary is where a codec is derived or a value crosses one: a data's field, a
     * newtype's base, a behavior's input and its output.
     */
    public static boolean hasExternalForm(Type t, Symbols symbols) {
        return answers(t, Requires.EXTERNAL_FORM, symbols);
    }

    /**
     * The part of {@code t} that has no external form, or null when the whole of it has one. What it
     * is, is part of the answer: a function and a tuple are both refused at a boundary and for the
     * same reason, but what an author should write instead differs, so a reader that reports one must
     * not report it as the other.
     *
     * <p>The decision is {@link #answers}'s; this only walks to where it was made. A type that
     * answers no and is not a collection is itself the part that cannot cross.
     */
    public static Type withoutExternalForm(Type t, Symbols symbols) {
        if (answers(t, Requires.EXTERNAL_FORM, symbols)) {
            return null;
        }
        return switch (t) {
            case Type.ListOf l -> withoutExternalForm(l.element(), symbols);
            case Type.SetOf s -> withoutExternalForm(s.element(), symbols);
            case Type.OptionOf o -> withoutExternalForm(o.element(), symbols);
            case Type.MapOf m -> {
                Type inKey = withoutExternalForm(m.key(), symbols);
                yield inKey != null ? inKey : withoutExternalForm(m.value(), symbols);
            }
            default -> t;
        };
    }

    /** The type a field's written type stands for. A field whose type is not representable at the
     * boundary is refused where the data is checked; the type is read the same way either way. */
    public static Type fieldType(Ast.Field f) {
        return f.type() instanceof Ast.TypeRef ref ? ref.denotes() : resolveTerm(f.type(), null);
    }

    /** The type one written term stands for. */
    public static Type resolveTerm(Ast.TypeTerm t, Symbols symbols) {
        return switch (t) {
            case Ast.TypeRef ref -> ref.denotes();
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
        for (Ast.TypeTerm t : ret.cases()) {
            members.add(resolveTerm(t, symbols));
        }
        if (members.size() == 1) {
            return members.get(0);
        }
        Set<TypeName> names = new LinkedHashSet<>();
        for (Type m : members) {
            TypeName name = memberName(m);
            if (name == null) {
                throw CompileException.of(Diagnostic
                                .at(ret.pos()).say(new TypeMessage.NotAUnionMember(Type.show(m))).build());
            }
            names.add(name);
        }
        return Type.union(names);
    }

    /**
     * The case name a union member goes by: a data type's own name, or the name a primitive is
     * written under in a match arm ({@code Int} in {@code Int | NoAnswer}). Null for a type that
     * cannot be a member.
     *
     * <p>A member has to be nominal and has to tell itself apart from the other members at run time,
     * because that is what a {@code match} arm and a Java {@code switch} both dispatch on. A
     * collection fails the second: its type argument is erased, so {@code List<Order>} and
     * {@code List<Item>} are one runtime type and no arm could choose between them. An
     * {@code Option} and a function fail it the same way. That they also have no arm form to write
     * is the surface showing the same fact.
     */
    static TypeName memberName(Type m) {
        if (m instanceof Type.Ref r) {
            return r.name();
        }
        if (m == Type.INT) return TypeName.primitive("Int");
        if (m == Type.STRING) return TypeName.primitive("String");
        if (m == Type.BOOL) return TypeName.primitive("Bool");
        if (m == Type.DECIMAL) return TypeName.primitive("Decimal");
        if (m == Type.DATE) return TypeName.primitive("Date");
        if (m == Type.DATETIME) return TypeName.primitive("DateTime");
        return null;
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
        if (t instanceof Type.Union u) {
            return u.members();
        }
        TypeName name = memberName(t);
        return name == null ? Set.of() : Set.of(name);
    }

    /** Case names of a stage output, treating a {@code Raw} encoder output as the case {@code "Raw"}
     * so it can be unioned with propagated error cases (spec §sequential-composition, §case-propagation). */
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
        Set<TypeName> names = namesOf(sub);
        return !names.isEmpty() && sup instanceof Type.Union u && u.members().containsAll(names);
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
            if (d instanceof Ast.SumData sum && caseNames(sum).contains(ref.name())
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
            names = caseNames(sum);
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

    /** A sum's cases: what each name it lists denotes. */
    public static List<TypeName> caseNames(Ast.SumData sum) {
        List<TypeName> names = new ArrayList<>();
        for (Ast.Name c : sum.cases()) {
            names.add(c.denotes());
        }
        return names;
    }

    /**
     * What a sum's encoding adds to this case, or a behavior's answer to this member — read from the
     * declaration the name denotes (spec §encoder-derivation). A braced data lays its fields beside the
     * discriminator, a data with no contents is the discriminator alone, and a newtype or a primitive
     * puts its standalone representation under {@code "value"}.
     *
     * <p>The one place code generation classifies a case's representation. The encoder of a named
     * sum, the encoder of a behavior's anonymous answer, the decoder that hands a case what it wrote
     * and the jOOQ row all ask it, and each of them working it out a different way is how the
     * envelope came to have two owners.
     *
     * <p>A fixture asks something else. Its question is which form a value takes at the position it
     * is written in, which the shape alone does not answer — the same newtype is bare at its own type
     * and wrapped inside a sum — so {@code NeutralForm} reads the position and this stays about the
     * declaration.
     */
    public static CaseShape caseShape(TypeName name, Symbols symbols) {
        if (name.isPrimitive()) {
            return CaseShape.WRAPPED;   // a bare scalar carries no key the discriminator could go on
        }
        return switch (symbols.get(name)) {
            case Ast.Data d when d.newtype() -> CaseShape.WRAPPED;
            case Ast.Data _ -> CaseShape.PRODUCT;
            case Ast.UnitData _ -> CaseShape.UNIT;
            case null, default -> throw new IllegalStateException(
                    "`" + name + "` stands as a case but denotes no data");
        };
    }

    /**
     * Whether anything in {@code module} has a type the compiler could not work out.
     *
     * <p>Asked after the module is checked, never before: the error type exists so that the check can
     * carry on past one mistake, and a hole in one declaration must not silence every other definition
     * in the file.
     *
     * <p>It is asked as well as {@link Names.Sound}, not instead of it, because a module can hold a
     * hole without having reported anything: an import of a module that is here and unusable leaves
     * the names it was to bring denoting nothing, and what is wrong was reported on that module's
     * source. No pass added later can forget this gate — a pass that cannot work a type out puts an
     * error type in, and this finds it wherever it is.
     */
    public static boolean holdsAnErroneousType(Ast.Module module) {
        for (Ast.Def def : module.defs()) {
            if (def instanceof Ast.Data d) {
                for (Ast.Field f : d.fields()) {
                    if (erroneous(f.type())) {
                        return true;
                    }
                }
                for (Ast.Name include : d.includes()) {
                    if (include.denotes() != null && include.denotes().isUnresolved()) {
                        return true;
                    }
                }
            }
            if (def instanceof Ast.SumData sum) {
                for (Ast.Name c : sum.cases()) {
                    if (c.denotes() != null && c.denotes().isUnresolved()) {
                        return true;
                    }
                }
            }
        }
        for (Ast.BehaviorDef b : module.behaviors()) {
            if (b instanceof Ast.SpecBehavior spec) {
                for (Ast.Param param : spec.params()) {
                    if (erroneous(param.type())) {
                        return true;
                    }
                }
                if (erroneous(spec.ret())) {
                    return true;
                }
                for (Ast.Name constructs : spec.constructs()) {
                    if (constructs.denotes() != null && constructs.denotes().isUnresolved()) {
                        return true;
                    }
                }
            } else if (b instanceof Ast.PipeBehavior pipe && erroneous(pipe.declaredOut())) {
                return true;
            }
        }
        for (Ast.FnDef fn : module.fns()) {
            for (Ast.FnParam param : fn.params()) {
                if (erroneous(param.type())) {
                    return true;
                }
            }
            if (erroneous(fn.declaredReturn())) {
                return true;
            }
        }
        return false;
    }

    private static boolean erroneous(Ast.RetType ret) {
        return ret != null && ret.cases().stream().anyMatch(TypeOps::erroneous);
    }

    private static boolean erroneous(Ast.TypeTerm term) {
        return switch (term) {
            case null -> false;
            case Ast.FnType ft ->
                    ft.params().stream().anyMatch(TypeOps::erroneous) || erroneous(ft.result());
            case Ast.TypeRef ref -> {
                if (ref.denotes() instanceof Type.Erroneous) {
                    yield true;
                }
                if (ref.tupleElems() != null
                        && ref.tupleElems().stream().anyMatch(TypeOps::erroneous)) {
                    yield true;
                }
                yield erroneous(ref.arg());
            }
        };
    }

    /** Whether a {@code from} value can be assigned where {@code to} is expected. Lists are
     * covariant, and a data-like type widens to the set of leaf cases it can be — so a list of
     * a sum's cases is assignable to a list of the sum (spec §sum-data, §unmarked-output). */
    public static boolean assignable(Type from, Type to, Symbols symbols) {
        if (from.equals(to)) {
            return true;
        }
        if (from instanceof Type.Erroneous || to instanceof Type.Erroneous) {
            // Something here has no type because the compiler already said why. Answering "yes"
            // reports nothing further about it: the alternative is one mistake arriving again at
            // every position the value it produced flowed into.
            return true;
        }
        if (from == Type.NOTHING) {
            return true;   // the empty list's bottom element assigns into any element type (ADR-0028)
        }
        if (from instanceof Type.Never) {
            // nothing arrives from there, so no value of the wrong type can (spec §match)
            return true;
        }
        // immutable collections are element-covariant: A <: S makes a List/Map/Option of A
        // assignable to one of S. Sound because they cannot be mutated (spec §collections), so no write can
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
     * on its elements (spec §unmarked-output, §if). An empty collection's bottom takes on the other side's
     * type, at the top or at any depth, so a bare {@code Set.empty} accumulator joins the
     * {@code Set<Int>} the other arm grows and a {@code (Set.empty, [])} joins position by
     * position. */
    public static Type join(Type a, Type b) {
        if (a.equals(b)) {
            return a;
        }
        if (a instanceof Type.Erroneous || b instanceof Type.Erroneous) {
            return Type.ERRONEOUS;   // one side has no type; neither has the joined position
        }
        if (BottomInfer.isBottom(a)) {
            return b;
        }
        if (BottomInfer.isBottom(b)) {
            return a;
        }
        // An arm that answers `unreachable` contributes no case to the join: what the position holds
        // is what the arms that answer a value hold (spec §match).
        if (a instanceof Type.Never) {
            return b;
        }
        if (b instanceof Type.Never) {
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
     * The type two branches take when they do not join on their own but the position expects a union
     * both are members of. A primitive joins nothing by itself — {@code Int} against {@code Decimal}
     * is a mistake wherever no union was asked for, and that error is worth keeping — so a branch
     * answering the value and a branch answering the reason there is none are settled by the output
     * that was written. Null when {@code expected} does not admit both.
     */
    static Type joinAt(Type expected, Type a, Type b) {
        if (!(expected instanceof Type.Union) || !subtypeOf(a, expected) || !subtypeOf(b, expected)) {
            return null;
        }
        Set<TypeName> names = new LinkedHashSet<>(namesOf(a));
        names.addAll(namesOf(b));
        return caseSetType(names);
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
        unify(param, arg, bindings, symbols, pos, what, true);
    }

    /**
     * What {@code arg} settles of the variables {@code param} carries, refusing nothing.
     *
     * <p>For a caller that requires each argument afterwards, against the parameter type this walk
     * settled and at the argument's own position. Refusing here as well would answer the same
     * mismatch twice, and this reading is the one with no argument in its hands: it is given two
     * types and the position of the call they belong to, so the caret it can offer is the callee's
     * — which is the one part of the line a reader has already been told is not the problem.
     */
    public static void bindVars(Type param, Type arg, Map<String, Type> bindings, Symbols symbols) {
        unify(param, arg, bindings, symbols, null, null, false);
    }

    private static void unify(Type param, Type arg, Map<String, Type> bindings,
                              Symbols symbols, SourcePos pos, String what, boolean refusing) {
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
                } else if (refusing && !assignable(arg, bound, symbols)
                        && !assignable(bound, arg, symbols)) {
                    throw CompileException.of(Diagnostic
                                    .at(pos)
                                    .diff(Type.show(arg, bound), Type.show(bound, arg)).say(new TypeMessage.ItExpectedOneTypeAndGotAnother(what, Type.show(bound), Type.show(arg))).build());
                }
            }
            case Type.ListOf p when arg instanceof Type.ListOf a ->
                    unify(p.element(), a.element(), bindings, symbols, pos, what, refusing);
            case Type.MapOf p when arg instanceof Type.MapOf a -> {
                unify(p.key(), a.key(), bindings, symbols, pos, what, refusing);
                unify(p.value(), a.value(), bindings, symbols, pos, what, refusing);
            }
            case Type.SetOf p when arg instanceof Type.SetOf a ->
                    unify(p.element(), a.element(), bindings, symbols, pos, what, refusing);
            case Type.OptionOf p when arg instanceof Type.OptionOf a ->
                    unify(p.element(), a.element(), bindings, symbols, pos, what, refusing);
            case Type.TupleOf p when arg instanceof Type.TupleOf a
                    && p.elements().size() == a.elements().size() -> {
                for (int i = 0; i < p.elements().size(); i++) {
                    unify(p.elements().get(i), a.elements().get(i), bindings, symbols, pos, what, refusing);
                }
            }
            case Type.FnOf p when arg instanceof Type.FnOf a && p.params().size() == a.params().size() -> {
                for (int i = 0; i < p.params().size(); i++) {
                    unify(p.params().get(i), a.params().get(i), bindings, symbols, pos, what, refusing);
                }
                unify(p.result(), a.result(), bindings, symbols, pos, what, refusing);
            }
            default -> {
                if (refusing && !assignable(arg, param, symbols)) {
                    throw CompileException.of(Diagnostic
                                    .at(pos)
                                    .diff(Type.show(arg, param), Type.show(param, arg)).say(new TypeMessage.ItExpectedOneTypeAndGotAnother(what, Type.show(param), Type.show(arg))).build());
                }
            }
        }
    }

    /**
     * {@code t} with every type variable still free read as the bottom.
     *
     * <p>A declaration's arguments are what bind its variables, so one with no arguments leaves any
     * the context did not pin standing. That is the same situation an empty {@code []} is in, and it
     * takes the same answer: the bottom unifies with whatever a later position fixes (ADR-0028).
     *
     * <p>Only for a declaration written with no parameter list. Elsewhere a variable left free is a
     * signature that could not be worked out, and reading it as the bottom would hide that.
     */
    public static Type toBottom(Type t) {
        return switch (t) {
            case Type.Var _ -> Type.NOTHING;
            case Type.ListOf l -> Type.list(toBottom(l.element()));
            case Type.MapOf m -> Type.map(toBottom(m.key()), toBottom(m.value()));
            case Type.SetOf s -> Type.set(toBottom(s.element()));
            case Type.OptionOf o -> Type.option(toBottom(o.element()));
            default -> t;
        };
    }

    /** {@code t} with each variable a declaration wrote replaced by what {@code bindings} gives it,
     * by the name the declaration wrote — so two occurrences of one variable stay one. */
    public static Type substituteVars(Type t, Map<String, Type> bindings) {
        return substitute(t, bindings);
    }

    /** {@code t} with each variable of an application replaced by what {@code bindings} gives it. */
    public static Type substituteMetas(Type t, Map<Type.MetaVar, Type> bindings) {
        return switch (t) {
            case Type.MetaVar m -> bindings.getOrDefault(m, m);
            case Type.ListOf l -> Type.list(substituteMetas(l.element(), bindings));
            case Type.MapOf m -> Type.map(substituteMetas(m.key(), bindings),
                    substituteMetas(m.value(), bindings));
            case Type.SetOf s -> Type.set(substituteMetas(s.element(), bindings));
            case Type.OptionOf o -> Type.option(substituteMetas(o.element(), bindings));
            case Type.FnOf f -> {
                List<Type> params = new ArrayList<>();
                for (Type p : f.params()) {
                    params.add(substituteMetas(p, bindings));
                }
                yield Type.fn(params, substituteMetas(f.result(), bindings));
            }
            case Type.TupleOf tup -> {
                List<Type> es = new ArrayList<>();
                for (Type e : tup.elements()) {
                    es.add(substituteMetas(e, bindings));
                }
                yield Type.tuple(es);
            }
            default -> t;
        };
    }

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
    /**
     * Two effective members of {@code out} that go by one written name, or null when every member's
     * name is its own. Asked after a named sum is expanded to its leaves, since the leaves are what a
     * {@code match} arm names and what the {@code "type"} discriminator carries — a sum contributes
     * its cases, not itself.
     */
    static TypeName[] ambiguousMembers(Type out, Symbols symbols) {
        Map<String, TypeName> byName = new LinkedHashMap<>();
        for (TypeName member : leafCases(out, symbols)) {
            TypeName seen = byName.put(member.name(), member);
            if (seen != null && !seen.equals(member)) {
                return new TypeName[] {seen, member};
            }
        }
        return null;
    }

    /**
     * The first leaf of {@code out} that declares a field named {@code key}, or null when none does.
     * A leaf lays its fields flatly beside the discriminator, so a field of that name and the tag
     * want one key: whichever is written second is the only one left. Asked of the leaves, since a
     * nested sum contributes its cases rather than itself.
     */
    static TypeName memberCarryingField(Type out, String key, Symbols symbols) {
        for (TypeName member : leafCases(out, symbols)) {
            if (declaresField(member, key, symbols)) {
                return member;
            }
        }
        return null;
    }

    /** Whether {@code name} declares a field called {@code key}, spread fields included. A newtype's
     * one field is named {@code value} and a unit has none, so only a record can. */
    static boolean declaresField(TypeName name, String key, Symbols symbols) {
        return symbols.get(name) instanceof Ast.Data data && !data.newtype()
                && fieldTypes(data, symbols).containsKey(key);
    }

    /**
     * The cases a position of this type can be, when it can be more than one thing: the leaf cases of
     * a union or of a named sum, and nothing otherwise.
     *
     * <p>What a row's expected arm is held against, and what an adequacy report counts as declared. The
     * two have to agree — a report that read a wider set than the rows are checked against would name a
     * case no row is allowed to write — so the rule is here rather than stated twice.
     */
    public static Set<TypeName> outputCases(Type t, Symbols symbols) {
        return t instanceof Type.Union || t instanceof Type.Ref ? leafCases(t, symbols) : Set.of();
    }

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
                for (TypeName caseName : caseNames(s)) {
                    collectLeafCases(Type.ref(caseName), symbols, out, visiting);
                }
            } else {
                out.add(name);
            }
        }
    }

    /**
     * The binding each of {@code data}'s fields introduces inside its own invariant.
     *
     * <p>An invariant reads its declaration's fields, and reads them as the bindings they are. Which
     * binding each is is answered here and nowhere else, so the pass that resolves an invariant and
     * the pass that emits it reach the same one. A field name is unique within a declaration, which
     * is what lets the answer be keyed by it; the order the map iterates in says nothing, and no
     * reader may take one from it.
     *
     * <p>What is fixed is the numbering: a field is numbered among the fields of the declaration
     * that declares it, in the order that declaration writes them. An include brings a field in
     * without renumbering it, so the two passes agree however either of them reaches it.
     *
     * <p>{@code declared} is which declaration this is, and is asked of the caller because
     * {@code data} cannot say: a declaration carries the name it was written under and not the module
     * that wrote it. Worked out here from that name it would be worked out against whoever is
     * reading, and a reader of another module's declaration would bind its fields under its own name
     * — a different binding for the same field, and the clauses carried in with the declaration
     * resolve against nothing. A caller reading its own declaration passes {@link Symbols#own}; a
     * caller reading one it reached passes the name it reached it by.
     */
    public static Map<String, BindingId> fieldBindings(TypeName declared, Ast.Data data,
                                                       Symbols symbols) {
        Map<String, BindingId> bindings = new LinkedHashMap<>();
        walkFields(data, declared, symbols, new LinkedHashSet<>(), bindings);
        return bindings;
    }

    /**
     * Every field {@code data} has, each with the binding the declaration that declares it gives it.
     *
     * <p>A field brought in by an include keeps the binding of the declaration it was written in,
     * because the invariant that reads it was written there too and is carried in with it. So a
     * declaration binds its own fields and the fields underneath, and an invariant reads the same
     * binding wherever it is checked or emitted.
     *
     * <p>A walk of its own, not the one {@link #fieldTypes} makes, because it answers where that one
     * cannot: this runs while the declaration is being resolved, where an include may not yet say
     * what it denotes, and a field has a name whether or not its type has been worked out. It
     * therefore reaches the fields in an order of its own, which is why nothing reads one off the
     * result. An include that names nothing is skipped, and a name an include repeats keeps the
     * declaration's own — both are refused where the declaration is checked, and refusing them twice
     * says nothing more.
     */
    private static void walkFields(Ast.Data data, TypeName declared, Symbols symbols,
                                   Set<TypeName> seen, Map<String, BindingId> out) {
        BindingOwner owner = new BindingOwner.OfFields(declared);
        int ordinal = 0;
        for (Ast.Field field : data.fields()) {
            out.putIfAbsent(field.name(), new BindingId(owner, ordinal++));
        }
        for (Ast.Name include : data.includes()) {
            TypeName source = include.denotes() != null
                    ? include.denotes() : symbols.resolve(include.written());
            if (source != null && seen.add(source)
                    && symbols.get(source) instanceof Ast.Data included) {
                walkFields(included, source, symbols, seen, out);
            }
        }
    }

    /** Effective field name → type (included data flattened first, then own fields). */
    public static Map<String, Type> fieldTypes(Ast.Data data, Symbols symbols) {
        Map<String, Type> types = new LinkedHashMap<>();
        // Which spread put each field here, so a collision names the group that supplied the earlier
        // one. Reporting it against the taking data names a declaration that, where both fields came
        // through spreads, holds no such field at all.
        Map<String, String> suppliedBy = new LinkedHashMap<>();
        for (Ast.Name inc : data.includes()) {
            TypeName included = inc.denotes();
            if (!(symbols.get(included) instanceof Ast.Data id)) {
                throw CompileException.of(Diagnostic.at(inc.name().reportedAt())
                        .say(new DataMessage.SpreadIsNotAProductData(inc.written()))
                        .build());
            }
            for (Map.Entry<String, Type> e : fieldTypes(id, symbols).entrySet()) {
                if (types.put(e.getKey(), e.getValue()) != null) {
                    throw CompileException.of(Diagnostic.at(inc.name().reportedAt())
                            .say(new DataMessage.SpreadFieldCollision(
                                    e.getKey(), inc.written(), suppliedBy.get(e.getKey())))
                            .build());
                }
                suppliedBy.put(e.getKey(), "..." + inc.written());
            }
        }
        for (Ast.Field f : data.fields()) {
            if (types.put(f.name(), fieldType(f)) != null) {
                throw CompileException.of(Diagnostic.at(f.pos())
                        .say(new DataMessage.FieldIsDeclaredMoreThanOnceIn(f.name(), data.name()))
                        .build());
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
        for (Ast.Field f : data.fields()) {
            if (f.name().equals(field)) {
                return fieldType(f);
            }
        }
        for (Ast.Name inc : data.includes()) {
            Ast.Data included = spreadTarget(inc, symbols);
            if (included != null) {
                Type t = fieldType(included, field, symbols);
                if (t != null) {
                    return t;
                }
            }
        }
        return null;
    }

    /** The product data a spread names, or null when nothing here denotes it or what it denotes is
     * not a product. Only {@link #fieldTypes} turns those into a diagnostic, and every declared data
     * goes through it; the readers asked about one field or one invariant answer for what they see. */
    private static Ast.Data spreadTarget(Ast.Name inc, Symbols symbols) {
        return symbols.get(inc.denotes()) instanceof Ast.Data d ? d : null;
    }

    /** Whether a data has a field of that name, without resolving any type. */
    public static boolean hasField(Ast.Data data, String field, Symbols symbols) {
        for (Ast.Field f : data.fields()) {
            if (f.name().equals(field)) {
                return true;
            }
        }
        for (Ast.Name inc : data.includes()) {
            Ast.Data included = spreadTarget(inc, symbols);
            if (included != null && hasField(included, field, symbols)) {
                return true;
            }
        }
        return false;
    }

    /**
     * The fields a sum exposes: those contributed by a data that every one of its cases spreads,
     * transitively. What holds of every case is a property of the sum, and a spread is nominal
     * (ADR-0012), so what makes the fields shared is that the author wrote `...Common` in each case —
     * not that two cases happen to agree on a field name, which would be the structural reading
     * ADR-0012 declines. Empty when the cases share no spread, so the read stays the error it is.
     */
    public static Map<String, Type> commonSpreadFields(Ast.SumData sum, Symbols symbols) {
        return commonSpreadFields(leafCases(sum, symbols), symbols);
    }

    /** As {@link #commonSpreadFields(Ast.SumData, Symbols)}, for cases already flattened to leaves. */
    public static Map<String, Type> commonSpreadFields(List<TypeName> cases, Symbols symbols) {
        if (cases == null || cases.isEmpty()) {
            return Map.of();
        }
        Set<TypeName> common = null;
        for (TypeName c : cases) {
            Set<TypeName> spreads = symbols.get(c) instanceof Ast.Data d
                    ? spreadAncestors(d, symbols) : Set.of();
            if (common == null) {
                common = new LinkedHashSet<>(spreads);
            } else {
                common.retainAll(spreads);
            }
            if (common.isEmpty()) {
                return Map.of();
            }
        }
        Map<String, Type> fields = new LinkedHashMap<>();
        for (TypeName ancestor : common) {
            if (symbols.get(ancestor) instanceof Ast.Data d) {
                fields.putAll(fieldTypes(d, symbols));
            }
        }
        return fields;
    }

    /** Every data reachable from {@code data} through spreads, transitively — the set two cases are
     * intersected on. The data itself is not one of them: a case is not its own shared part. */
    private static Set<TypeName> spreadAncestors(Ast.Data data, Symbols symbols) {
        Set<TypeName> out = new LinkedHashSet<>();
        collectSpreadAncestors(data, symbols, out);
        return out;
    }

    private static void collectSpreadAncestors(Ast.Data data, Symbols symbols, Set<TypeName> out) {
        for (Ast.Name inc : data.includes()) {
            Ast.Data included = spreadTarget(inc, symbols);
            if (included != null && out.add(inc.denotes())) {
                collectSpreadAncestors(included, symbols, out);
            }
        }
    }

    /**
     * All invariant clauses that apply to a data, in the order a failure is decided by: the clauses of
     * the data it spreads first, then its own, each in the order it is written.
     *
     * <p>A clause keeps the name it was declared with wherever it arrives from, so a spread carries not
     * only the rule but what an attempt on the spreading type calls it.
     */
    public static List<Ast.InvariantClause> effectiveInvariants(Ast.Data data, Symbols symbols) {
        return effectiveInvariants(null, data, symbols, _ -> null);
    }

    /**
     * The same, reading each declaration's clauses through {@code form} rather than off the
     * declaration.
     *
     * <p>An analysis that reads a representation other than the settled one asks for it by the
     * declaration's name, and gets the settled one wherever {@code form} has nothing to say — which
     * is every declaration another module made, since what travels is the settled form.
     */
    public static List<Ast.InvariantClause> effectiveInvariants(
            TypeName named, Ast.Data data, Symbols symbols,
            Function<TypeName, List<Ast.InvariantClause>> form) {
        List<Ast.InvariantClause> invs = new ArrayList<>();
        for (Declared one : declaredInvariants(named, data, symbols, form)) {
            invs.add(one.clause());
        }
        return invs;
    }

    /**
     * A clause and the declaration that wrote it.
     *
     * <p>A clause reaching a type through a spread is that type's to hold and the other type's to
     * have written, and a reader told which clause failed on a data that declares none of its own is
     * told about a declaration they would not find. {@code declaredOn} is null where the walk was
     * not given a name to start from.
     */
    public record Declared(TypeName declaredOn, Ast.InvariantClause clause) {}

    /**
     * The same clauses {@link #effectiveInvariants} answers, each with the declaration it was written
     * on.
     *
     * <p>Flattening them loses which spread brought which, and what is reported of an unproven clause
     * is the name the author wrote — so what is asked for here is the pair, and the flat list is
     * taken from it rather than walked again.
     */
    public static List<Declared> declaredInvariants(
            TypeName named, Ast.Data data, Symbols symbols,
            Function<TypeName, List<Ast.InvariantClause>> form) {
        List<Declared> invs = new ArrayList<>();
        for (Ast.Name inc : data.includes()) {
            Ast.Data id = spreadTarget(inc, symbols);
            if (id != null) {
                invs.addAll(declaredInvariants(inc.denotes(), id, symbols, form));
            }
        }
        List<Ast.InvariantClause> own = named == null ? null : form.apply(named);
        for (Ast.InvariantClause clause : own != null ? own : data.invariants()) {
            invs.add(new Declared(named, clause));
        }
        return invs;
    }

    /** The type a newtype wraps ({@code data X = Y} gives {@code Y}), or null when {@code name} is not
     * a newtype — the implicit inner field is {@code value}. */
    public static Type newtypeInner(TypeName name, Symbols symbols) {
        if (symbols.get(name) instanceof Ast.Data d && d.newtype()) {
            return fieldTypes(d, symbols).get("value");
        }
        return null;
    }

    /** Whether {@code name} is a newtype over {@code String} ({@code data X = String}). A key is a
     *  JSON object's key, so what a newtype wraps has to be text already; a newtype over another
     *  base would be converted and rendered differently, which is a case of its own in
     *  {@link BoundaryMapKey} rather than a widening of this. */
    private static boolean isStringNewtype(TypeName name, Symbols symbols) {
        return symbols.get(name) instanceof Ast.Data d && d.newtype()
                && d.fields().size() == 1
                && d.fields().get(0).type() instanceof Ast.TypeRef base && "String".equals(base.name());
    }

    /**
     * Whether {@code key} may stand as a {@code Map} key in a signature. This is not the question the
     * codecs ask: a type variable may be written — the {@code core}'s {@code Map<'k, 'a>} signatures
     * are — and stands for a key rather than being one, so it is admissible and classifies as
     * nothing. Everything else is admissible exactly when it classifies.
     */
    public static boolean isMapKeyAdmissibleInSignature(Type key, Symbols symbols) {
        return key instanceof Type.Var || classifyConcreteMapKey(key, symbols) != null;
    }

    /**
     * What a concrete {@code key} would be converted through, or null when it has no representation
     * at all. A map's external form is a JSON object, whose keys are strings, so a key that has one
     * renders as and parses from a bare string: {@code String} itself, a String-backed newtype
     * (ADR-0040), a temporal as the ISO form a {@code Date} field already travels as, or an
     * enumeration as its case's name (issue #161).
     *
     * <p>This classifies and does not admit. Whether a key of a given representation may stand in a
     * given position is the position's own question — a behavior's boundary refuses a name the
     * language declares of its own operations, and a fixture's position asks something else again —
     * so what comes back says what the key converts through and nothing about where it may be
     * written. A boundary turns one into a {@link BoundaryMapKey} once it has admitted the name.
     *
     * <p>The classification itself is this function's alone. A reader that builds a decoder, renders
     * an encoder's keys or lowers a key into the codec IR takes what it needs from the result; none
     * of them asks the type again.
     */
    public static MapKeyRepresentation classifyConcreteMapKey(Type key, Symbols symbols) {
        if (key == Type.STRING) {
            return new MapKeyRepresentation.Text();
        }
        if (key == Type.DATE) {
            return new MapKeyRepresentation.Date();
        }
        if (key == Type.DATETIME) {
            return new MapKeyRepresentation.DateTime();
        }
        if (key instanceof Type.Ref r) {
            if (isStringNewtype(r.name(), symbols)) {
                return new MapKeyRepresentation.StringNewtype(r.name());
            }
            if (isUnitOnlySum(key, symbols)) {
                return new MapKeyRepresentation.UnitEnum(r.name());
            }
        }
        return null;
    }

    /**
     * Whether every case of a sum is a unit data — an enumeration, carrying nothing but which case it
     * is. What holds of every case is a property of the sum: such a sum crosses the boundary as that
     * case's name, a bare string, so it renders and parses in key position like any other string
     * (issue #161, ADR-0040). A sum with even one field-bearing case keeps the discriminator object.
     */
    public static boolean isUnitOnlySum(Type t, Symbols symbols) {
        return t instanceof Type.Ref ref && symbols.get(ref.name()) instanceof Ast.SumData sum
                && isUnitOnlySum(sum, symbols);
    }

    public static boolean isUnitOnlySum(Ast.SumData sum, Symbols symbols) {
        List<TypeName> leaves = leafCases(sum, symbols);
        if (leaves.isEmpty()) {
            return false;
        }
        for (TypeName leaf : leaves) {
            if (!(symbols.get(leaf) instanceof Ast.UnitData)) {
                return false;
            }
        }
        return true;
    }

    /** A sum's leaf cases in declaration order, nested sums flattened where they are written. */
    public static List<TypeName> leafCases(Ast.SumData sum, Symbols symbols) {
        Set<TypeName> leaves = new LinkedHashSet<>();
        for (TypeName c : caseNames(sum)) {
            leaves.addAll(leafCases(Type.ref(c), symbols));
        }
        return List.copyOf(leaves);
    }

    /** The key of the first {@code Map} inside {@code t} that cannot cross the boundary, or null when
     * every one can — what a data field or a behavior's input/output is checked against. */
    public static Type nonBoundaryMapKey(Type t, Symbols symbols) {
        if (t instanceof Type.MapOf m && !isMapKeyAdmissibleInSignature(m.key(), symbols)) {
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


    /**
     * Whether {@code name} is a type a model declares, as against one the language declares of its own
     * operations. The two are already told apart where construction is governed — what a compilation
     * declares answers to {@code constructs} and the language's vocabulary does not — and the same
     * line decides what a boundary may carry.
     *
     * <p>A primitive is neither: it is a scalar the boundary writes, with no declaration anywhere.
     * {@code Raw} is spelled as one and answers no, having no declaration to be found.
     */
    static boolean declaredByAModel(TypeName name, Symbols symbols) {
        if (name.isPrimitive()) {
            return !"Raw".equals(name.name());
        }
        return symbols.declaredByCompilation(name);
    }

    public static boolean isSingleValueNewtype(Type t, Symbols symbols) {
        return t instanceof Type.Ref ref
                && symbols.get(ref.name()) instanceof Ast.Data d && d.newtype();
    }

    /** The ordered primitives: the ones the JVM carries as {@link Comparable}, so {@code <}/{@code >}
     * and {@code sort} work on them (spec §primitives, §stdlib-list). */
    static boolean isOrdered(Type t) {
        return switch (t) {
            case Type.Prim p -> switch (p) {
                case INT, STRING, DECIMAL, DATE, DATETIME -> true;
                case BOOL, RAW -> false;
            };
            case Type.Ref _, Type.ListOf _, Type.MapOf _, Type.SetOf _, Type.OptionOf _,
                 Type.Union _, Type.FnOf _, Type.Open _, Type.Nothing _, Type.Never _,
                 Type.TupleOf _, Type.Erroneous _ -> false;
        };
    }

    /**
     * The enumeration two operands of {@code <}/{@code <=}/{@code >}/{@code >=} are ordered by, or
     * null when they are not both values of one. Either side may name it: {@code stage < Won}
     * carries the order on the left, and a case listed by two sums takes the one it is compared with.
     */
    public static TypeName comparisonEnumeration(Type lt, Type rt, Symbols symbols) {
        TypeName named = orderingEnumeration(lt, symbols);
        if (named == null) {
            named = orderingEnumeration(rt, symbols);
        }
        return named != null && isValueOfEnumeration(lt, named, symbols)
                && isValueOfEnumeration(rt, named, symbols) ? named : null;
    }

    /** Whether {@code t} is that enumeration, one of its leaves, or a union of them. */
    private static boolean isValueOfEnumeration(Type t, TypeName enumeration, Symbols symbols) {
        if (t instanceof Type.Union union) {
            for (TypeName member : union.members()) {
                if (!isValueOfEnumeration(Type.ref(member), enumeration, symbols)) {
                    return false;
                }
            }
            return !union.members().isEmpty();
        }
        return t instanceof Type.Ref ref && (ref.name().equals(enumeration)
                || (symbols.get(enumeration) instanceof Ast.SumData sum
                    && leafCases(sum, symbols).contains(ref.name())));
    }

    /**
     * The enumeration that orders a value of {@code t} — a sum all of whose cases are unit data,
     * ordered by the order they are declared in, which is the order a state machine moves through
     * (F#'s discriminated union, Haskell's derived {@code Ord}, Java's ordinal; issue #161). It is
     * the type itself when it is one, or the single one that lists it as a case.
     *
     * <p>Null when the type is not one and when more than one enumeration lists it: a unit data may
     * be a case of two sums, which place it differently, so no one order is the value's own. The
     * order therefore belongs to the sum and not to the case value.
     */
    public static TypeName orderingEnumeration(Type t, Symbols symbols) {
        Set<TypeName> candidates = orderingCandidates(t, symbols);
        return candidates != null && candidates.size() == 1 ? candidates.iterator().next() : null;
    }

    /**
     * Every enumeration that could order a value of {@code t}, or null when it is not a value of one.
     * A list literal of case values (`[ Negotiation, Prospecting ]`) is typed as the union of their
     * types, and what orders it is the enumeration that lists all of them — so the candidates are
     * intersected across the members rather than each member having to name one on its own.
     */
    private static Set<TypeName> orderingCandidates(Type t, Symbols symbols) {
        if (t instanceof Type.Union union) {
            Set<TypeName> shared = null;
            for (TypeName member : union.members()) {
                Set<TypeName> owners = orderingCandidates(Type.ref(member), symbols);
                if (owners == null) {
                    return null;
                }
                if (shared == null) {
                    shared = new LinkedHashSet<>(owners);
                } else {
                    shared.retainAll(owners);
                }
            }
            return shared;
        }
        if (!(t instanceof Type.Ref ref)) {
            return null;
        }
        if (symbols.get(ref.name()) instanceof Ast.SumData sum) {
            return isUnitOnlySum(sum, symbols) ? Set.of(ref.name()) : null;
        }
        if (!(symbols.get(ref.name()) instanceof Ast.UnitData)) {
            return null;
        }
        // A sum and its cases are declared together (a case declared elsewhere cannot join a union
        // here, E1606), so every enumeration that lists this case is in the case's own module. Asking
        // that module rather than what is visible keeps the answer the same in every module that
        // reads the value.
        Set<TypeName> owners = new LinkedHashSet<>();
        for (Ast.Def def : symbols.declaredIn(ref.name().module()).values()) {
            if (def instanceof Ast.SumData s && isUnitOnlySum(s, symbols)
                    && leafCases(s, symbols).contains(ref.name())) {
                owners.add(ref.name().sibling(s.name()));
            }
        }
        return owners;
    }

    /**
     * The underlying base of a type: itself, or — for a single-value newtype ({@code data X = Y}) —
     * the base of its {@code value} type, recursively (so {@code 管理職 = レベル = Int} bases to Int).
     * A newtype's value is what its comparison and equality read.
     */
    public static Type base(Type t, Symbols symbols) {
        return newtypeSpine(t, symbols).terminal();
    }

    /**
     * The names wrapped round a value and what is left when they are off.
     *
     * <p>The one walk. How far a newtype reaches is a fact about the declarations and not about who
     * is asking, and two readers deciding it apart is what #461 was: a comparison reaching the base
     * while the range beside it stopped at the first name. Everything that needs to know derives from
     * here — what a value is carried as, which declarations' rules apply to it, whether it is a
     * number at all.
     *
     * <p>Stops on a name already worn, so a declaration reachable from itself ends the walk rather
     * than repeating it, and stops where a newtype's {@code value} is not declared.
     */
    public static NewtypeSpine newtypeSpine(Type t, Symbols symbols) {
        List<Layer> layers = new ArrayList<>();
        Set<TypeName> worn = new LinkedHashSet<>();
        Type at = t;
        while (isSingleValueNewtype(at, symbols) && worn.add(((Type.Ref) at).name())) {
            Ast.Data data = (Ast.Data) symbols.get(((Type.Ref) at).name());
            layers.add(new Layer(((Type.Ref) at).name(), data));
            Type inner = fieldTypes(data, symbols).get("value");
            if (inner == null) {
                break;
            }
            at = inner;
        }
        return new NewtypeSpine(List.copyOf(layers), at);
    }

    /** The names a value wears, and the type underneath them. */
    public record NewtypeSpine(List<Layer> layers, Type terminal) {}

    /**
     * One name a value wears, and the declaration it is written by.
     *
     * <p>Kept together because a rule is read at a layer and reported by the declaration that wrote
     * it — a failure names a clause of a type, and dropping which type that was leaves a diagnostic
     * with nothing to point at.
     */
    public record Layer(TypeName named, Ast.Data data) {}

    /**
     * The names wrapped round a value of {@code t}, outermost first.
     *
     * <p>One place says how far a newtype reaches, because more than one thing needs to know: what a
     * construction has to satisfy, what a position's range is, what a comparison of two such values
     * compares. Each working it out for itself is how they came to disagree about a value wearing two
     * names — the projection reading through and the range reader stopping at the first.
     *
     * <p>Stops on a name already worn, so a declaration that wraps its own kind ends the walk rather
     * than repeating it. A type that is not a newtype has one layer or none.
     */
    public static List<Layer> newtypeChain(Type t, Symbols symbols) {
        return newtypeSpine(t, symbols).layers();
    }

    /**
     * The {@code Int} or {@code Decimal} a value of {@code t} is carried as, reaching through as many
     * newtypes as it is written with, or {@code null} where it is carried as neither.
     *
     * <p>The language's own reading: a comparison of two such values compares the numbers underneath
     * however many names are wrapped round them (ADR-0047). Not what arithmetic asks — that is
     * {@link #directNumericNewtypeBase} and stops at one layer, which the language means.
     */
    public static Type numericBase(Type t, Symbols symbols) {
        Type carried = newtypeSpine(t, symbols).terminal();
        return carried == Type.INT || carried == Type.DECIMAL ? carried : null;
    }

    /** What a single-value newtype directly wraps (one level, so a newtype over a newtype answers
     * with that newtype), or {@code null} for anything that is not one. */
    static Type wrapped(Type t, Symbols symbols) {
        if (isSingleValueNewtype(t, symbols)) {
            return fieldTypes((Ast.Data) symbols.get(((Type.Ref) t).name()), symbols).get("value");
        }
        return null;
    }

    /** The Int or Decimal that a single-value newtype directly wraps (one level), or {@code null}
     * (a non-newtype, or a newtype over a non-numeric or over another newtype). */
    static Type directNumericNewtypeBase(Type t, Symbols symbols) {
        Type inner = wrapped(t, symbols);
        return inner == Type.INT || inner == Type.DECIMAL ? inner : null;
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

    public static Type primType(LeafScalar kind) {
        return switch (kind) {
            case STRING -> Type.STRING;
            case INT -> Type.INT;
            case BOOL -> Type.BOOL;
            case DECIMAL -> Type.DECIMAL;
            case DATE -> Type.DATE;
            case DATETIME -> Type.DATETIME;
        };
    }

    /**
     * The type {@code ref} denotes, computed from the reference and the scope it was written in. The
     * one place a written type becomes a {@link Type}; {@code Resolve} calls it once per reference and
     * everything else reads {@link Ast.TypeRef#denotes()}. Its own arguments are already resolved, so
     * a nested reference is read rather than recomputed.
     */
    static Type denoted(Ast.TypeRef ref, Symbols symbols) {
        if (ref.isTuple()) {
            List<Type> elems = new ArrayList<>();
            for (Ast.TypeTerm e : ref.tupleElems()) {
                elems.add(resolveTerm(e, symbols));
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
            // 制約違反 is no longer a writable case: an invariant violation aborts (spec §algebraic-types,
            // §violation-destination).
            case "List" -> Type.list(typeArg(ref, symbols, "list", 4, "List needs a type argument, e.g. List<Int>"));
            case "Set" -> {
                // a set holds no duplicates, which is a question about equality of its elements
                Type element = typeArg(ref, symbols, "set", 3,
                        "Set needs a type argument, e.g. Set<String>");
                requireEquality(element, symbols, ref, false,
                        "a Set has no duplicate elements, and a function has no value to compare");
                yield Type.set(element);
            }
            case "Option" -> Type.option(typeArg(ref, symbols, "option", 6, "Option needs a type argument"));
            case "Map" -> {
                // The key is not restricted here: a map that stays inside a behavior body renders
                // nothing, so it may be keyed by any value (`List.groupBy` already builds such maps).
                // What a key must satisfy is the boundary — see #isBoundaryMapKey, checked where a
                // type is a data field or a behavior's input/output.
                Type value = typeArg(ref, symbols, "map", 3, "Map needs a value type, e.g. Map<String, Int>");
                Type key = ref.tupleElems() == null
                        ? Type.STRING : resolveTerm(ref.tupleElems().get(0), symbols);
                requireEquality(key, symbols, ref, true,
                        "a Map finds a value by its key, and a function has no value to compare");
                yield Type.map(key, value);
            }
            default -> {
                if (ref.name().startsWith("'")) {
                    yield Type.var(ref.name());   // a type variable, admitted only in the core
                }
                TypeName resolved = symbols.resolve(ref.name());
                if (resolved != null) {
                    yield resolved.isUnresolved() ? Type.ERRONEOUS : Type.ref(resolved);
                }
                // A union's case names a type where a type goes. A `match` arm has always read it
                // that way; a declaration reads it the same, which is what lets `Int |
                // DivisionByZero` be written rather than only met. Asked after the module's own
                // declarations, so a name a model declares keeps its meaning.
                TypeName asCase = symbols.resolveCase(ref.name());
                if (asCase != null && !asCase.isUnresolved()) {
                    yield Type.ref(asCase);
                }
                throw unknownType(ref, symbols);
            }
        };
    }

    /**
     * A collection inside a type that would have to compare something it cannot. Which collection it
     * is, is part of the answer: a {@code Set} asks whether two elements are equal and a {@code Map}
     * whether two keys are, and those are different requirements, so a reader that reports one must
     * not report it as the other.
     */
    public sealed interface UncomparableIn {
        Type type();

        record SetElement(Type type) implements UncomparableIn {}

        record MapKey(Type type) implements UncomparableIn {}
    }

    /**
     * The {@code Set} element or {@code Map} key inside {@code t} that cannot be compared, or null
     * when every one of them can. Walks the whole type, so a set nested in a list or under a map's
     * value is asked the same question as one written on its own.
     */
    public static UncomparableIn uncomparableCollection(Type t, Symbols symbols) {
        return switch (t) {
            case Type.SetOf s -> !supportsEquality(s.element(), symbols)
                    ? new UncomparableIn.SetElement(s.element())
                    : uncomparableCollection(s.element(), symbols);
            case Type.MapOf m -> !supportsEquality(m.key(), symbols)
                    ? new UncomparableIn.MapKey(m.key())
                    : firstNonNull(uncomparableCollection(m.key(), symbols),
                            uncomparableCollection(m.value(), symbols));
            case Type.ListOf l -> uncomparableCollection(l.element(), symbols);
            case Type.OptionOf o -> uncomparableCollection(o.element(), symbols);
            case Type.TupleOf tu -> {
                for (Type e : tu.elements()) {
                    UncomparableIn bad = uncomparableCollection(e, symbols);
                    if (bad != null) {
                        yield bad;
                    }
                }
                yield null;
            }
            default -> null;
        };
    }

    private static UncomparableIn firstNonNull(UncomparableIn a, UncomparableIn b) {
        return a != null ? a : b;
    }

    /** Refuses a collection whose element or key a function makes uncomparable. */
    private static void requireEquality(Type t, Symbols symbols, Ast.TypeRef at, boolean aMapKey,
                                        String message) {
        if (!supportsEquality(t, symbols)) {
            throw CompileException.of(Diagnostic.at(at.pos())
                    .say(aMapKey
                            ? new TypeMessage.AMapKeyIsComparedAndAFunctionIsNot(Type.show(t))
                            : new TypeMessage.ASetElementIsComparedAndAFunctionIsNot(Type.show(t)))
                    .build());
        }
    }

    /** The single type argument of a built-in constructor, or the error that says it is missing. */
    private static Type typeArg(Ast.TypeRef ref, Symbols symbols, String key, int width,
                                String message) {
        if (ref.arg() == null) {
            throw CompileException.of(Diagnostic.at(ref.pos(), width)
                    .say(switch (key) {
                        case "list" -> new TypeMessage.AListNeedsItsElementType();
                        case "set" -> new TypeMessage.ASetNeedsItsElementType();
                        case "map" -> new TypeMessage.AMapNeedsItsValueType();
                        default -> new TypeMessage.AnOptionNeedsItsTypeArgument();
                    })
                    .build());
        }
        return resolveTerm(ref.arg(), symbols);
    }

    /**
     * A written type name nothing here denotes. A qualified name says which of three things went
     * wrong, since the qualifier narrows it: the qualifier names no module, the module declares no
     * such type, or it declares it and does not expose it.
     */
    private static CompileException unknownType(Ast.TypeRef ref, Symbols symbols) {
        return unknownType(ref.written(), symbols);
    }

    static CompileException unknownType(WrittenName written, Symbols symbols) {
        String canonical = written.canonical();
        int dot = canonical.lastIndexOf('.');
        if (dot >= 0) {
            String qualifier = canonical.substring(0, dot);
            String name = canonical.substring(dot + 1);
            String module = symbols.moduleOfQualifier(qualifier);
            if (module == null) {
                return CompileException.of(Diagnostic.say(new ModuleMessage.NoModuleOfThatName(qualifier, name))
                                .at(written.reportedAt())
                                .suggestion(Suggest.candidate(qualifier, symbols.qualifiers()))
                                .build());
            }
            boolean declared = symbols.contains(new TypeName(module, name));
            return CompileException.of(Diagnostic.at(written.reportedAt())
                            .say(declared
                                    ? new ModuleMessage.ItIsDeclaredThereAndNotExposed(name, module)
                                    : new ModuleMessage.TheModuleDeclaresNoSuchQualifiedName(name,
                                            module))
                            .suggestion(Suggest.candidate(name, symbols.declaredIn(module).keySet()))
                            .build());
        }
        Set<String> known = symbols.namesInScope();
        return CompileException.of(Diagnostic
                        .at(written.reportedAt())
                        
                        .suggestion(Suggest.candidate(canonical, known))
                        .say(new NameMessage.NoTypeOfThatName(written.quoted())).build());
    }
}
