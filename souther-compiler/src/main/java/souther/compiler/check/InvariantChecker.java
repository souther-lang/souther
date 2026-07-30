package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.check.NumericDomain.LinearForm;
import souther.compiler.check.NumericDomain.Rel;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.Type;

import java.math.BigDecimal;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Function;

/**
 * The intraprocedural invariant-discharge check (spec §invariant-discharge). It walks a behavior's body threading a
 * {@link NumericDomain} — seeded from the input newtypes' invariants and refined along each
 * {@code guard}/{@code if} guard (a {@code guard} is already an {@code if} here) — and, at every
 * construction whose invariant is expressible in the domain, asks whether the guards
 * <em>discharge</em> it. A construction the domain proves must violate its invariant on a reachable
 * path is a compile error (the path-sensitive generalization of the constant check {@code 金額(-5)});
 * one it cannot prove is a warning (a possible abort — guard it, or reify the relation into a type
 * invariant). An invariant it cannot express is left opaque (no diagnostic; the run-time check stays),
 * so every flagged construction has a guard the domain can verify.
 *
 * <p>The walk mirrors {@link TotalityChecker}: a {@code switch} over {@code Ast.Expr} threading an
 * immutable environment. It is fail-open — any internal error is swallowed so an analysis bug can
 * never reject a valid program.
 */
final class InvariantChecker {

    record Findings(List<CompileException> errors, List<Diagnostic> warnings) {}

    /** A stdlib combinator whose closure (argument {@code closureArg}) is handed each element of its
     * container argument ({@code listArg}) as closure parameter {@code elementParam} — mirrors
     * {@link TotalityChecker}'s table, so a construction inside a {@code List.map}/{@code fold} closure
     * is analyzed with the element bound to the container's element type ({@link #elementType}). */
    private record Combinator(int closureArg, int elementParam, int listArg) {}

    private static final Map<String, Combinator> COMBINATORS = Map.ofEntries(
            Map.entry("List.fold", new Combinator(0, 1, 2)),
            Map.entry("List.foldFrom", new Combinator(0, 1, 2)),
            Map.entry("List.foldr", new Combinator(0, 1, 2)),
            Map.entry("List.map", new Combinator(0, 0, 1)),
            Map.entry("List.filter", new Combinator(0, 0, 1)),
            Map.entry("List.all", new Combinator(0, 0, 1)),
            Map.entry("List.any", new Combinator(0, 0, 1)),
            Map.entry("List.find", new Combinator(0, 0, 1)),
            Map.entry("List.partition", new Combinator(0, 0, 1)),
            Map.entry("List.concatMap", new Combinator(0, 0, 1)),
            Map.entry("List.filterMap", new Combinator(0, 0, 1)),
            Map.entry("List.sortBy", new Combinator(0, 0, 1)),
            Map.entry("List.groupBy", new Combinator(0, 0, 1)),
            Map.entry("List.indexBy", new Combinator(0, 0, 1)),
            Map.entry("List.allUniqueBy", new Combinator(0, 0, 1)),
            Map.entry("List.indexedMap", new Combinator(0, 1, 1)),
            Map.entry("Map.fold", new Combinator(0, 2, 2)),
            Map.entry("Map.map", new Combinator(0, 1, 1)),
            Map.entry("Map.filter", new Combinator(0, 1, 1)),
            Map.entry("Map.update", new Combinator(1, 0, 2)),
            Map.entry("Map.upsert", new Combinator(2, 0, 3)),
            Map.entry("Set.fold", new Combinator(0, 1, 2)),
            Map.entry("Set.map", new Combinator(0, 0, 1)),
            Map.entry("Set.filter", new Combinator(0, 0, 1)),
            Map.entry("Set.partition", new Combinator(0, 0, 1)),
            Map.entry("Option.map", new Combinator(0, 0, 1)));

    /** The pure, total stdlib calls whose result is a number the domain can name: the size of a
     * container or a string. Each becomes an atom keyed by the call written over its argument's path
     * — {@code List.length(b.items)} — so an invariant clause and a guard naming the same container
     * name the same atom, and the guard discharges the clause. The argument must be a nameable path:
     * {@code List.length(List.map(f, xs))} is not this atom, and nothing relates the two. */
    private static final Set<String> SIZE_CALLS =
            Set.of("List.length", "String.length", "Set.size", "Map.size");

    private final Symbols symbols;
    private final List<CompileException> errors = new ArrayList<>();
    private final List<Diagnostic> warnings = new ArrayList<>();

    private InvariantChecker(Symbols symbols) {
        this.symbols = symbols;
    }

    /** Analyzes one behavior body against its input types. Never throws. */
    static Findings analyze(Ast.Expr body, Map<String, Type> params, Symbols symbols) {
        InvariantChecker c = new InvariantChecker(symbols);
        try {
            NumericDomain d = NumericDomain.top();
            for (Map.Entry<String, Type> p : params.entrySet()) {
                d = c.seedParam(p.getKey(), p.getValue(), d);
            }
            c.walk(body, d, new HashMap<>(params));
        } catch (RuntimeException _) {
            // fail-open: the run-time invariant check remains the backstop
        }
        return new Findings(c.errors, c.warnings);
    }

    // --- the walk ------------------------------------------------------------------------------

    private void walk(Ast.Expr e, NumericDomain d, Map<String, Type> types) {
        checkIfConstruction(e, d, types, false);
        switch (e) {
            case Ast.If iff -> {
                walk(iff.cond(), d, types);
                walk(iff.then(), assumeCond(iff.cond(), d, types, true), types);
                walk(iff.els(), assumeCond(iff.cond(), d, types, false), types);
            }
            case Ast.IfConstructed ic -> {
                // The attempt's own construction cannot abort — a failing invariant is the else
                // branch — so it is checked for a decided violation and never warned about as a
                // possible one. Its field values are walked on their own so a construction nested
                // inside an argument is still an ordinary, aborting one.
                checkIfConstruction(ic.construct(), d, types, true);
                Ast.forEachChild(ic.construct(), child -> walk(child, d, types));
                Map<String, Type> t2 = new HashMap<>(types);
                NumericDomain d2 = rebind(d, ic.binder());
                Type built = typeExpr(ic.construct(), types);
                if (built != null) {
                    t2.put(ic.binder(), built);
                    d2 = seedParam(ic.binder(), built, d2);   // on this branch the invariant holds
                }
                walk(ic.then(), d2, t2);
                walk(ic.els(), d, types);
            }
            case Ast.LetIn li -> {
                walk(li.value(), d, types);
                Map<String, Type> t2 = new HashMap<>(types);
                Type vt = typeExpr(li.value(), types);
                if (vt != null) {
                    t2.put(li.name(), vt);
                }
                LinearForm vf = affineOf(li.value(), types);
                NumericDomain d2 = rebind(d, li.name());
                if (isNumeric(vt) && vf != null) {
                    d2 = d2.assign(li.name(), vf);
                }
                walk(li.body(), d2, t2);
            }
            case Ast.Match m -> {
                walk(m.scrutinee(), d, types);
                for (Ast.Case c : m.cases()) {
                    Map<String, Type> t2 = new HashMap<>(types);
                    NumericDomain d2 = d;
                    if (c.binding() != null) {
                        d2 = rebind(d, c.binding());
                        if (c.caseTypes().size() == 1) {
                            Type bound = MatchElaborator.caseBindType(c.caseTypes().get(0).denotes());
                            if (bound != null) {
                                t2.put(c.binding(), bound);
                            }
                        }
                    }
                    walk(c.body(), d2, t2);
                }
            }
            case Ast.Call call -> walkCall(call, d, types);
            default -> Ast.forEachChild(e, child -> walk(child, d, types));
        }
    }

    /** Walks a call, binding a combinator closure's element parameter to the list's element type (and
     * seeding its invariant) so a construction inside the closure is analyzed rather than left opaque. */
    private void walkCall(Ast.Call call, NumericDomain d, Map<String, Type> types) {
        Combinator combo = COMBINATORS.get(call.fn());
        for (int i = 0; i < call.args().size(); i++) {
            Ast.Expr arg = call.args().get(i);
            if (combo != null && i == combo.closureArg() && arg instanceof Ast.Block step
                    && combo.elementParam() < step.params().size()
                    && combo.listArg() < call.args().size()) {
                Type elem = elementType(typeExpr(call.args().get(combo.listArg()), types));
                Map<String, Type> t2 = new HashMap<>(types);
                String p = step.params().get(combo.elementParam());
                NumericDomain d2 = rebind(d, p);
                if (elem != null) {
                    t2.put(p, elem);
                    d2 = seedParam(p, elem, d2);   // the element carries its type's invariant
                }
                walk(step.body(), d2, t2);
            } else {
                walk(arg, d, types);
            }
        }
    }

    // --- construction detection & discharge check ----------------------------------------------

    private void checkIfConstruction(Ast.Expr e, NumericDomain d, Map<String, Type> types,
                                     boolean attempted) {
        switch (e) {
            case Ast.NewData nd when nd.spreads().isEmpty() -> {
                if (symbols.get(nd.typeName().denotes()) instanceof Ast.Data type) {
                    Map<String, LinearForm> forms = new HashMap<>();
                    Map<String, String> paths = new HashMap<>();
                    for (Ast.FieldInit fi : nd.inits()) {
                        LinearForm f = affineOf(fi.value(), types);
                        if (f != null) {
                            forms.put(fi.name(), f);
                        }
                        String p = pathKey(fi.value(), types);
                        if (p != null) {
                            paths.put(fi.name(), p);
                        }
                    }
                    check(type, new Bindings(forms::get, paths::get), d, nd.pos(), attempted);
                }
            }
            case Ast.Binary bin when isArith(bin.op()) -> {
                if (typeExpr(bin, types) instanceof Type.Ref r
                        && symbols.get(r.name()) instanceof Ast.Data type && type.newtype()) {
                    LinearForm value = affineOf(bin, types);
                    if (value != null) {
                        // an arithmetic result is a form, not a location, so it names no path
                        check(type, new Bindings(name -> "value".equals(name) ? value : null, _ -> null),
                                d, bin.pos(), attempted);
                    }
                }
            }
            default -> { }
        }
    }

    /** How an invariant's leaf names resolve at a construction site: to the affine form of what the
     * field is being given, and to that value's canonical path — so a size call over the field names
     * the same atom the body names when it calls the same function on the same container. */
    private record Bindings(Function<String, LinearForm> form, Function<String, String> path) {}

    /** Runs the discharge check for a construction of {@code type} whose field values resolve through
     * {@code binds}. A definite violation is an error; an unproven one a warning; a fully-discharged
     * or non-expressible invariant is silent. An {@code attempted} construction raises no warning:
     * what the warning reports is a possible abort, and an attempt takes its else branch instead. */
    private void check(Ast.Data type, Bindings binds, NumericDomain d, SourcePos pos,
                       boolean attempted) {
        List<Ast.Expr> invs = TypeOps.effectiveInvariants(type, symbols);
        if (invs.isEmpty()) {
            return;
        }
        List<Constraint> constraints = new ArrayList<>();
        for (Ast.Expr inv : invs) {
            List<Constraint> cs = invConstraints(inv, binds);
            if (cs == null) {
                return;   // some part is not expressible in the domain — leave the whole opaque
            }
            constraints.addAll(cs);
        }
        NumericDomain dom = withSizeBounds(d, constraints);
        boolean possible = false;
        for (Constraint c : constraints) {
            if (dom.refutes(c.form(), c.rel())) {
                errors.add(CompileException.of(
                        Diagnostic.of("E2010", "check.invariant.violation").title("check.invariant.title")
                                .at(pos).args(type.name()).build(),
                        "constructing `" + type.name() + "` here violates its invariant on a reachable path"));
                return;
            }
            if (!dom.entails(c.form(), c.rel())) {
                possible = true;
            }
        }
        if (possible && !attempted) {
            warnings.add(
                    Diagnostic.of("E2011", "check.invariant.unproven").title("check.invariant.title")
                            .at(pos).args(type.name()).hint("check.invariant.reify", type.name())
                            .warning().build());
        }
    }

    // --- invariant / condition -> constraints --------------------------------------------------

    private record Constraint(LinearForm form, Rel rel) {}

    /** The constraints an invariant expression contributes under {@code binds} (field/{@code value}
     * name -> what it is being given), or {@code null} if any part is not expressible. */
    private List<Constraint> invConstraints(Ast.Expr inv, Bindings binds) {
        if (inv instanceof Ast.Binary b && b.op() == Ast.BinOp.AND) {
            List<Constraint> l = invConstraints(b.left(), binds);
            List<Constraint> r = invConstraints(b.right(), binds);
            if (l == null || r == null) {
                return null;
            }
            List<Constraint> both = new ArrayList<>(l);
            both.addAll(r);
            return both;
        }
        if (inv instanceof Ast.Binary b) {
            Rel rel = relOf(b.op());
            if (rel != null) {
                LinearForm la = affine(b.left(), resolveLeaf(binds));
                LinearForm ra = affine(b.right(), resolveLeaf(binds));
                return la == null || ra == null ? null : List.of(new Constraint(la.minus(ra), rel));
            }
        }
        return null;
    }

    /** The domain told that every size atom the constraints name is non-negative. The atom enters the
     * domain only through the clause naming it, so without this the fact a container's size is never
     * negative is not available to discharge a clause that asks only for that. */
    private static NumericDomain withSizeBounds(NumericDomain d, List<Constraint> constraints) {
        NumericDomain out = d;
        for (Constraint c : constraints) {
            for (String atom : c.form().coefs().keySet()) {
                if (isSizeAtom(atom)) {
                    out = out.assume(LinearForm.atom(atom), Rel.GE);
                }
            }
        }
        return out;
    }

    /** Refines {@code d} by asserting {@code cond} (or its negation). Non-comparison conditions and
     * non-affine operands leave the domain unchanged (sound). */
    private NumericDomain assumeCond(Ast.Expr cond, NumericDomain d, Map<String, Type> types, boolean positive) {
        if (cond instanceof Ast.Binary b && b.op() == Ast.BinOp.AND && positive) {
            return assumeCond(b.right(), assumeCond(b.left(), d, types, true), types, true);
        }
        if (cond instanceof Ast.Binary b) {
            Rel rel = relOf(b.op());
            if (rel != null) {
                LinearForm la = affineOf(b.left(), types);
                LinearForm ra = affineOf(b.right(), types);
                Rel eff = positive ? rel : negateRel(rel);
                if (la != null && ra != null && eff != null) {
                    return d.assume(la.minus(ra), eff);
                }
            }
        }
        return d;
    }

    // --- seeding -------------------------------------------------------------------------------

    /** Seeds the domain with what a parameter's type guarantees: a numeric newtype's own invariant on
     * its value, or a product data's invariant over its fields (and one level of numeric-newtype
     * fields), each substituted onto the parameter's atom(s). Sound by closed construction — an input
     * of type T was built through T's checked constructor. */
    private NumericDomain seedParam(String name, Type t, NumericDomain d) {
        return seedAt(name, t, d, 0);
    }

    private NumericDomain seedAt(String path, Type t, NumericDomain d, int depth) {
        if (depth > 2 || !(t instanceof Type.Ref ref) || !(symbols.get(ref.name()) instanceof Ast.Data data)) {
            return d;
        }
        Map<String, Type> fields = TypeOps.fieldTypes(data, symbols);
        Function<String, String> resolvePath = fieldName -> {
            if (data.newtype() && fieldName.equals("value")) {
                return path;
            }
            return fields.containsKey(fieldName) ? path + "." + fieldName : null;
        };
        Bindings binds = new Bindings(
                fieldName -> {
                    String p = resolvePath.apply(fieldName);
                    return p == null ? null : LinearForm.atom(p);
                },
                resolvePath);
        NumericDomain out = d;
        for (Ast.Expr inv : TypeOps.effectiveInvariants(data, symbols)) {
            List<Constraint> cs = invConstraints(inv, binds);
            if (cs != null) {
                for (Constraint c : cs) {
                    out = out.assume(c.form(), c.rel());
                }
            }
        }
        if (!data.newtype()) {
            for (Map.Entry<String, Type> f : fields.entrySet()) {
                out = seedAt(path + "." + f.getKey(), f.getValue(), out, depth + 1);
            }
        }
        return out;
    }

    // --- affine forms --------------------------------------------------------------------------

    /** The shared affine walk: literals and {@code +}/{@code -} compose; every other node is handed to
     * {@code leaf} (which decides whether it is an atom, a resolved field, or opaque). */
    private LinearForm affine(Ast.Expr e, Function<Ast.Expr, LinearForm> leaf) {
        return switch (e) {
            case Ast.IntLit i -> LinearForm.constant(BigDecimal.valueOf(i.value()));
            case Ast.DecimalLit dd -> LinearForm.constant(dd.value());
            case Ast.Neg n -> negate(affine(n.operand(), leaf));
            case Ast.Binary b when b.op() == Ast.BinOp.ADD ->
                    add(affine(b.left(), leaf), affine(b.right(), leaf), false);
            case Ast.Binary b when b.op() == Ast.BinOp.SUB ->
                    add(affine(b.left(), leaf), affine(b.right(), leaf), true);
            // scalar multiply by a constant (金額 * 2) is linear; `/` and a variable product are not
            // (a divide truncates for Int, and a variable factor is non-linear), so leave those opaque.
            case Ast.Binary b when b.op() == Ast.BinOp.MUL ->
                    scale(affine(b.left(), leaf), affine(b.right(), leaf));
            default -> leaf.apply(e);
        };
    }

    /** A linear form scaled by a constant, when one side is a bare constant (a scalar multiply); null
     * when neither side is constant (a non-linear product). */
    private static LinearForm scale(LinearForm a, LinearForm b) {
        if (a == null || b == null) {
            return null;
        }
        if (a.coefs().isEmpty()) {
            return b.times(a.constant());
        }
        return b.coefs().isEmpty() ? a.times(b.constant()) : null;
    }

    /** The affine form of a body expression: a numeric atom, a newtype construct's wrapped value, or
     * {@code null}. */
    private LinearForm affineOf(Ast.Expr e, Map<String, Type> types) {
        return affine(e, n -> {
            if (n instanceof Ast.NewData nd && nd.spreads().isEmpty() && nd.inits().size() == 1
                    && nd.inits().get(0).name().equals("value")
                    && numericNewtype(Type.ref(nd.typeName().denotes()))) {
                return affineOf(nd.inits().get(0).value(), types);
            }
            String atom = atomOf(n, types);
            return atom == null ? null : LinearForm.atom(atom);
        });
    }

    /** The leaf rule for an invariant expression: a bare name resolves to its field/{@code value}, and
     * a size call over one to that container's size atom. */
    private static Function<Ast.Expr, LinearForm> resolveLeaf(Bindings binds) {
        return n -> {
            String size = sizeAtom(n, arg -> invPath(arg, binds));
            if (size != null) {
                return LinearForm.atom(size);
            }
            return n instanceof Ast.Var v ? binds.form().apply(v.name()) : null;
        };
    }

    /** The path an invariant expression names at the construction site: a bare field name through the
     * bindings, then plain field steps. */
    private static String invPath(Ast.Expr e, Bindings binds) {
        return switch (e) {
            case Ast.Var v -> binds.path().apply(v.name());
            case Ast.FieldAccess fa -> {
                String base = invPath(fa.target(), binds);
                yield base == null ? null : base + "." + fa.field();
            }
            default -> null;
        };
    }

    private static LinearForm negate(LinearForm f) {
        return f == null ? null : f.negate();
    }

    private static LinearForm add(LinearForm a, LinearForm b, boolean subtract) {
        if (a == null || b == null) {
            return null;
        }
        return subtract ? a.minus(b) : a.plus(b);
    }

    /** The canonical atom key of a numeric location ({@code x}, {@code p.a}, a newtype's value) or of
     * a size call over a nameable container, or {@code null} if {@code e} is neither. */
    private String atomOf(Ast.Expr e, Map<String, Type> types) {
        String size = sizeAtom(e, arg -> pathKey(arg, types));
        if (size != null) {
            return size;
        }
        return isNumeric(typeExpr(e, types)) ? pathKey(e, types) : null;
    }

    /** The atom key of {@code SIZE_CALL(container)} when {@code path} can name the container, else
     * {@code null}. */
    private static String sizeAtom(Ast.Expr e, Function<Ast.Expr, String> path) {
        if (!(e instanceof Ast.Call call) || !SIZE_CALLS.contains(call.fn()) || call.args().size() != 1) {
            return null;
        }
        String arg = path.apply(call.args().get(0));
        return arg == null ? null : call.fn() + "(" + arg + ")";
    }

    private static boolean isSizeAtom(String atom) {
        int open = atom.indexOf('(');
        return open > 0 && atom.endsWith(")") && SIZE_CALLS.contains(atom.substring(0, open));
    }

    private String pathKey(Ast.Expr e, Map<String, Type> types) {
        return switch (e) {
            case Ast.Var v -> v.name();
            case Ast.FieldAccess fa -> {
                Type owner = typeExpr(fa.target(), types);
                if (fa.field().equals("value") && TypeOps.isSingleValueNewtype(owner, symbols)) {
                    yield pathKey(fa.target(), types);   // a newtype's .value is the same location
                }
                String base = pathKey(fa.target(), types);
                yield base == null ? null : base + "." + fa.field();
            }
            default -> null;
        };
    }

    /** The domain with every fact rooted at {@code name} dropped, because a binding of that name makes
     * it denote something else. An atom is rooted at a name when it is the name, a field chain from
     * it, or a size call over one. */
    private static NumericDomain rebind(NumericDomain d, String name) {
        return d.forgetIf(atom -> {
            int open = atom.indexOf('(');
            String path = isSizeAtom(atom) ? atom.substring(open + 1, atom.length() - 1) : atom;
            return path.equals(name) || path.startsWith(name + ".");
        });
    }

    // --- a minimal local typer (enough for atom/affine detection) ------------------------------

    private Type typeExpr(Ast.Expr e, Map<String, Type> types) {
        return switch (e) {
            case Ast.IntLit _ -> Type.INT;
            case Ast.DecimalLit _ -> Type.DECIMAL;
            case Ast.Var v -> types.get(v.name());
            case Ast.FieldAccess fa -> {
                Type owner = typeExpr(fa.target(), types);
                yield owner instanceof Type.Ref r && symbols.get(r.name()) instanceof Ast.Data d
                        ? TypeOps.fieldTypes(d, symbols).get(fa.field()) : null;
            }
            case Ast.NewData nd -> Type.ref(nd.typeName().denotes());
            case Ast.Neg n -> typeExpr(n.operand(), types);
            case Ast.Binary b when isArith(b.op()) -> arithType(b, types);
            default -> null;
        };
    }

    /** The result type of an arithmetic binary: the newtype for closed {@code +}/{@code -}
     * (via the checker's shared rule), else the numeric base, else {@code null}. */
    private Type arithType(Ast.Binary b, Map<String, Type> types) {
        Type lt = typeExpr(b.left(), types);
        Type rt = typeExpr(b.right(), types);
        // Closed `+`/`-` and scalar `*`/`/` both yield the newtype (the checker has already validated
        // admissibility, so a newtype operand here means the result is that newtype).
        if (isArith(b.op())) {
            Type nt = TypeOps.closedNewtypeArithResult(lt, rt, symbols);
            if (nt != null) {
                return nt;
            }
        }
        if (lt == Type.INT || lt == Type.DECIMAL) {
            return lt;
        }
        return rt == Type.INT || rt == Type.DECIMAL ? rt : null;
    }

    /** What a container hands its closure: a list's or set's element, a map's value (the key is the
     * other closure parameter and is not the one the table credits), an option's payload. */
    private static Type elementType(Type t) {
        if (t instanceof Type.ListOf list) {
            return list.element();
        }
        if (t instanceof Type.SetOf set) {
            return set.element();
        }
        if (t instanceof Type.MapOf map) {
            return map.value();
        }
        if (t instanceof Type.OptionOf opt) {
            return opt.element();
        }
        return null;
    }

    private boolean numericNewtype(Type t) {
        return TypeOps.directNumericNewtypeBase(t, symbols) != null;
    }

    private boolean isNumeric(Type t) {
        return t == Type.INT || t == Type.DECIMAL || numericNewtype(t);
    }

    // --- helpers -------------------------------------------------------------------------------

    private static boolean isArith(Ast.BinOp op) {
        return op == Ast.BinOp.ADD || op == Ast.BinOp.SUB || op == Ast.BinOp.MUL || op == Ast.BinOp.DIV;
    }

    private static Rel relOf(Ast.BinOp op) {
        return switch (op) {
            case GE -> Rel.GE;
            case GT -> Rel.GT;
            case LE -> Rel.LE;
            case LT -> Rel.LT;
            case EQ -> Rel.EQ;
            default -> null;
        };
    }

    private static Rel negateRel(Rel rel) {
        return switch (rel) {
            case GE -> Rel.LT;
            case GT -> Rel.LE;
            case LE -> Rel.GT;
            case LT -> Rel.GE;
            case EQ -> null;
        };
    }
}
