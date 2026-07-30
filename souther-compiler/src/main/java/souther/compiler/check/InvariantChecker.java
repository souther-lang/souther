package souther.compiler.check;

import souther.compiler.Prelude;
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
 * The intraprocedural invariant-discharge check (spec §invariant-discharge). It walks a behavior's
 * body threading what the guards have settled — a {@link NumericDomain} of relations and a
 * {@link PredicateFacts} of everything that states no relation — seeded from the input types'
 * invariants and refined along each {@code guard}/{@code if} guard (a {@code guard} is already an
 * {@code if} here). At every construction whose invariant it can carry, it asks whether the guards
 * <em>discharge</em> it. A construction proven to violate its invariant on a reachable path is a
 * compile error (the path-sensitive generalization of the constant check {@code 金額(-5)}); one it
 * cannot prove is a warning (a possible abort — guard it, or reify the relation into a type
 * invariant). An invariant naming something it cannot name is left opaque (no diagnostic; the
 * run-time check stays), so every flagged construction has a guard that discharges it.
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

    /** What the guards have settled on the current path: numeric relations, and predicates known to
     * hold or to fail. Threaded functionally through the walk, as the domain alone once was. */
    private record Known(NumericDomain numbers, PredicateFacts facts) {

        static Known top() {
            return new Known(NumericDomain.top(), PredicateFacts.none());
        }

        Known with(NumericDomain n) {
            return new Known(n, facts);
        }

        Known with(PredicateFacts f) {
            return new Known(numbers, f);
        }

        Known forgetIf(java.util.function.Predicate<String> drop) {
            return new Known(numbers.forgetIf(drop), facts.forgetIf(drop));
        }
    }

    /** Analyzes one behavior body against its input types. Never throws. */
    static Findings analyze(Ast.Expr body, Map<String, Type> params, Symbols symbols) {
        InvariantChecker c = new InvariantChecker(symbols);
        try {
            Known k = Known.top();
            for (Map.Entry<String, Type> p : params.entrySet()) {
                k = c.seedParam(p.getKey(), p.getValue(), k);
            }
            c.walk(body, k, new HashMap<>(params));
        } catch (RuntimeException _) {
            // fail-open: the run-time invariant check remains the backstop
        }
        return new Findings(c.errors, c.warnings);
    }

    // --- the walk ------------------------------------------------------------------------------

    private void walk(Ast.Expr e, Known k, Map<String, Type> types) {
        checkIfConstruction(e, k, types, false);
        switch (e) {
            case Ast.If iff -> {
                walk(iff.cond(), k, types);
                walk(iff.then(), assumeCond(iff.cond(), k, types, true), types);
                walk(iff.els(), assumeCond(iff.cond(), k, types, false), types);
            }
            case Ast.IfConstructed ic -> {
                // The attempt's own construction cannot abort — a failing invariant is the else
                // branch — so it is checked for a decided violation and never warned about as a
                // possible one. Its field values are walked on their own so a construction nested
                // inside an argument is still an ordinary, aborting one.
                checkIfConstruction(ic.construct(), k, types, true);
                Ast.forEachChild(ic.construct(), child -> walk(child, k, types));
                Map<String, Type> t2 = new HashMap<>(types);
                Known k2 = rebind(k, ic.binder());
                Type built = typeExpr(ic.construct(), types);
                if (built != null) {
                    t2.put(ic.binder(), built);
                    k2 = seedParam(ic.binder(), built, k2);   // on this branch the invariant holds
                }
                walk(ic.then(), k2, t2);
                walk(ic.els(), k, types);
            }
            case Ast.LetIn li -> {
                walk(li.value(), k, types);
                Map<String, Type> t2 = new HashMap<>(types);
                Type vt = typeExpr(li.value(), types);
                if (vt != null) {
                    t2.put(li.name(), vt);
                }
                LinearForm vf = affineOf(li.value(), types);
                Known k2 = rebind(k, li.name());
                if (isNumeric(vt) && vf != null) {
                    k2 = k2.with(k2.numbers().assign(li.name(), vf));
                }
                walk(li.body(), k2, t2);
            }
            case Ast.Match m -> {
                walk(m.scrutinee(), k, types);
                for (Ast.Case c : m.cases()) {
                    Map<String, Type> t2 = new HashMap<>(types);
                    Known k2 = k;
                    if (c.binding() != null) {
                        k2 = rebind(k, c.binding());
                        if (c.caseTypes().size() == 1) {
                            Type bound = MatchElaborator.caseBindType(c.caseTypes().get(0).denotes());
                            if (bound != null) {
                                t2.put(c.binding(), bound);
                            }
                        }
                    }
                    walk(c.body(), k2, t2);
                }
            }
            case Ast.Call call -> walkCall(call, k, types);
            default -> Ast.forEachChild(e, child -> walk(child, k, types));
        }
    }

    /** Walks a call, binding a combinator closure's element parameter to the list's element type (and
     * seeding its invariant) so a construction inside the closure is analyzed rather than left opaque. */
    private void walkCall(Ast.Call call, Known k, Map<String, Type> types) {
        Combinator combo = COMBINATORS.get(call.fn());
        for (int i = 0; i < call.args().size(); i++) {
            Ast.Expr arg = call.args().get(i);
            if (combo != null && i == combo.closureArg() && arg instanceof Ast.Block step
                    && combo.elementParam() < step.params().size()
                    && combo.listArg() < call.args().size()) {
                Type elem = elementType(typeExpr(call.args().get(combo.listArg()), types));
                Map<String, Type> t2 = new HashMap<>(types);
                String p = step.params().get(combo.elementParam());
                Known k2 = rebind(k, p);
                if (elem != null) {
                    t2.put(p, elem);
                    k2 = seedParam(p, elem, k2);   // the element carries its type's invariant
                }
                walk(step.body(), k2, t2);
            } else {
                walk(arg, k, types);
            }
        }
    }

    // --- construction detection & discharge check ----------------------------------------------

    private void checkIfConstruction(Ast.Expr e, Known k, Map<String, Type> types,
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
                    check(type, new Bindings(forms::get, paths::get,
                            TypeOps.fieldTypes(type, symbols)), k, nd.pos(), attempted);
                }
            }
            case Ast.Binary bin when isArith(bin.op()) -> {
                if (typeExpr(bin, types) instanceof Type.Ref r
                        && symbols.get(r.name()) instanceof Ast.Data type && type.newtype()) {
                    LinearForm value = affineOf(bin, types);
                    if (value != null) {
                        // an arithmetic result is a form, not a location, so it names no path
                        check(type, new Bindings(name -> "value".equals(name) ? value : null, _ -> null,
                                TypeOps.fieldTypes(type, symbols)), k, bin.pos(), attempted);
                    }
                }
            }
            default -> { }
        }
    }

    /** How an invariant's leaf names resolve at a construction site: to the affine form of what the
     * field is being given, and to that value's canonical path — so a size call over the field names
     * the same atom the body names when it calls the same function on the same container. */
    private record Bindings(Function<String, LinearForm> form, Function<String, String> path,
                            Map<String, Type> fields) {}

    /** Runs the discharge check for a construction of {@code type} whose field values resolve through
     * {@code binds}. A definite violation is an error; an unproven one a warning; a fully-discharged
     * or non-expressible invariant is silent. An {@code attempted} construction raises no warning:
     * what the warning reports is a possible abort, and an attempt takes its else branch instead. */
    private void check(Ast.Data type, Bindings binds, Known k, SourcePos pos, boolean attempted) {
        List<Ast.Expr> invs = TypeOps.effectiveInvariants(type, symbols);
        if (invs.isEmpty()) {
            return;
        }
        Obligations owed = Obligations.none();
        for (Ast.Expr inv : invs) {
            Obligations o = obligations(inv, binds);
            if (o == null) {
                return;   // some part is not expressible — leave the whole invariant opaque
            }
            owed = owed.and(o);
        }
        NumericDomain dom = withSizeBounds(k.numbers(), owed.numeric());
        boolean possible = false;
        for (Constraint c : owed.numeric()) {
            if (dom.refutes(c.form(), c.rel())) {
                reportViolation(type, pos);
                return;
            }
            if (!dom.entails(c.form(), c.rel())) {
                possible = true;
            }
        }
        for (Fact f : owed.predicates()) {
            if (k.facts().refutes(f.key(), f.positive())) {
                reportViolation(type, pos);
                return;
            }
            if (!k.facts().entails(f.key(), f.positive())) {
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

    private void reportViolation(Ast.Data type, SourcePos pos) {
        errors.add(CompileException.of(
                Diagnostic.of("E2010", "check.invariant.violation").title("check.invariant.title")
                        .at(pos).args(type.name()).build(),
                "constructing `" + type.name() + "` here violates its invariant on a reachable path"));
    }

    // --- invariant / condition -> constraints --------------------------------------------------

    private record Constraint(LinearForm form, Rel rel) {}

    /** A predicate stated of a term, by the term's canonical key. {@code positive} is false for a
     * clause written under {@code Bool.not}. */
    private record Fact(String key, boolean positive) {}

    /** What a construction owes: numeric relations the domain must prove, and predicates the guards
     * must have settled. */
    private record Obligations(List<Constraint> numeric, List<Fact> predicates) {

        private static final Obligations NONE = new Obligations(List.of(), List.of());

        static Obligations none() {
            return NONE;
        }

        static Obligations of(Constraint c) {
            return new Obligations(List.of(c), List.of());
        }

        static Obligations of(Fact f) {
            return new Obligations(List.of(), List.of(f));
        }

        Obligations and(Obligations o) {
            List<Constraint> n = new ArrayList<>(numeric);
            n.addAll(o.numeric);
            List<Fact> p = new ArrayList<>(predicates);
            p.addAll(o.predicates);
            return new Obligations(n, p);
        }
    }

    /** What an invariant expression owes under {@code binds} (field/{@code value} name -> what it is
     * being given), or {@code null} if it names nothing this check can carry. A comparison the domain
     * can express is owed to the domain; anything else is owed as a fact, which a guard stating the
     * same thing of the same term settles. */
    private Obligations obligations(Ast.Expr inv, Bindings binds) {
        return obligations(inv, binds, true);
    }

    private Obligations obligations(Ast.Expr inv, Bindings binds, boolean positive) {
        if (inv instanceof Ast.Binary b && b.op() == Ast.BinOp.AND && positive) {
            Obligations l = obligations(b.left(), binds, true);
            Obligations r = obligations(b.right(), binds, true);
            return l == null || r == null ? null : l.and(r);
        }
        if (inv instanceof Ast.Binary b && relOf(b.op()) != null) {
            Rel eff = positive ? relOf(b.op()) : negateRel(relOf(b.op()));
            LinearForm la = eff == null ? null : affine(b.left(), resolveLeaf(binds));
            LinearForm ra = eff == null ? null : affine(b.right(), resolveLeaf(binds));
            if (la != null && ra != null) {
                return Obligations.of(new Constraint(la.minus(ra), eff));
            }
        }
        Ast.Expr under = negated(inv);
        if (under != null) {
            return obligations(under, binds, !positive);
        }
        String key = termKey(inv, e -> invPath(e, binds), Map.of(), 0);
        return key == null ? null : Obligations.of(new Fact(key, positive));
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

    /** Refines {@code k} by asserting {@code cond} (or its negation): a comparison tightens the
     * numeric domain, a stdlib predicate settles a fact. A condition of neither shape, and an operand
     * outside the affine fragment, leave {@code k} unchanged (sound). */
    private Known assumeCond(Ast.Expr cond, Known k, Map<String, Type> types, boolean positive) {
        // `&&` asserted true gives both sides; `||` asserted false gives both sides negated.
        if (cond instanceof Ast.Binary b
                && (b.op() == Ast.BinOp.AND && positive || b.op() == Ast.BinOp.OR && !positive)) {
            return assumeCond(b.right(), assumeCond(b.left(), k, types, positive), types, positive);
        }
        if (cond instanceof Ast.Binary b) {
            Rel rel = relOf(b.op());
            Rel eff = rel == null ? null : positive ? rel : negateRel(rel);
            if (eff != null) {
                LinearForm la = affineOf(b.left(), types);
                LinearForm ra = affineOf(b.right(), types);
                if (la != null && ra != null) {
                    return k.with(k.numbers().assume(la.minus(ra), eff));
                }
            }
        }
        Ast.Expr under = negated(cond);
        if (under != null) {
            return assumeCond(under, k, types, !positive);
        }
        String key = termKey(cond, e -> pathKey(e, types), Map.of(), 0);
        return key == null ? k : k.with(k.facts().assume(key, positive));
    }

    /** What a negation is applied to, or {@code null} if {@code e} is not one. {@code Bool.not} is an
     * ordinary helper, so by here it is the body it expands to — {@code if b then false else true},
     * over a binding holding the argument. */
    private static Ast.Expr negated(Ast.Expr e) {
        if (e instanceof Ast.LetIn li) {
            Ast.Expr inner = negated(li.body());
            return inner instanceof Ast.Var v && v.name().equals(li.name()) ? li.value() : null;
        }
        return e instanceof Ast.If iff
                && iff.then() instanceof Ast.BoolLit t && !t.value()
                && iff.els() instanceof Ast.BoolLit f && f.value()
                ? iff.cond() : null;
    }

    // --- seeding -------------------------------------------------------------------------------

    /** Seeds the check with what a parameter's type guarantees: a numeric newtype's own invariant on
     * its value, a predicate its invariant states of it, or a product data's invariant over its fields
     * (and one level of fields), each substituted onto the parameter's own term. Sound by closed
     * construction — an input of type T was built through T's checked constructor. */
    private Known seedParam(String name, Type t, Known k) {
        return seedAt(name, t, k, 0);
    }

    private Known seedAt(String path, Type t, Known k, int depth) {
        if (depth > 2 || !(t instanceof Type.Ref ref) || !(symbols.get(ref.name()) instanceof Ast.Data data)) {
            return k;
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
                resolvePath, fields);
        Known out = k;
        // Each conjunct on its own: an input's invariant is a set of things that hold, and one the
        // check cannot express does not cost it the others.
        for (Ast.Expr inv : TypeOps.effectiveInvariants(data, symbols)) {
            for (Ast.Expr conjunct : conjuncts(inv)) {
                Obligations o = obligations(conjunct, binds);
                if (o == null) {
                    continue;
                }
                for (Constraint c : o.numeric()) {
                    out = out.with(out.numbers().assume(c.form(), c.rel()));
                }
                for (Fact f : o.predicates()) {
                    out = out.with(out.facts().assume(f.key(), f.positive()));
                }
            }
        }
        if (data.newtype()) {
            // A newtype's `.value` is the same location as the newtype, so what its base guarantees is
            // guaranteed of this very atom: `data Outer = Inner` carries Inner's invariant.
            out = seedAt(path, fields.get("value"), out, depth + 1);
        } else {
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
    private Function<Ast.Expr, LinearForm> resolveLeaf(Bindings binds) {
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
    private String invPath(Ast.Expr e, Bindings binds) {
        // A clause is a path over the declaration's own fields, read by the very rule a body path is
        // read by — so a newtype's `.value` is the same location on both sides — and then the field it
        // is rooted at is replaced by what the construction is giving that field. One rule for what a
        // location is, applied twice, rather than two rules that have to be kept agreeing.
        String local = pathKey(e, binds.fields());
        if (local == null) {
            return null;
        }
        int dot = local.indexOf('.');
        String root = dot < 0 ? local : local.substring(0, dot);
        String given = binds.path().apply(root);
        if (given == null) {
            return null;
        }
        return dot < 0 ? given : given + local.substring(dot);
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

    /** The conjuncts of an invariant expression, flattened. */
    private static List<Ast.Expr> conjuncts(Ast.Expr e) {
        if (e instanceof Ast.Binary b && b.op() == Ast.BinOp.AND) {
            List<Ast.Expr> out = new ArrayList<>(conjuncts(b.left()));
            out.addAll(conjuncts(b.right()));
            return out;
        }
        return List.of(e);
    }

    /**
     * The canonical key of an expression as a term, or {@code null} when nothing here can be named.
     * Two expressions with one key compute one value, which is the whole of what the fact set knows:
     * a guard and an invariant clause state the same predicate exactly when their calls key alike.
     *
     * <p>A location is asked of {@code site} — the body's path rule, or the invariant's rule for what
     * a field is being given — so the two sides meet on the construction's own names. A closure
     * parameter is keyed by where it is bound rather than by its spelling, so {@code r -> r.a} and
     * {@code row -> row.a} are one term while a free name inside the closure is still resolved
     * through {@code site} and so is part of the term. Anything outside this grammar keys as
     * {@code null}, and the clause reading it is left opaque.
     */
    private String termKey(Ast.Expr e, Function<Ast.Expr, String> site, Map<String, String> bound,
                           int depth) {
        String root = rootName(e);
        if (root != null) {
            String at = bound.get(root);
            return at != null ? chainOn(at, e) : site.apply(e);
        }
        return switch (e) {
            case Ast.IntLit i -> Long.toString(i.value());
            case Ast.DecimalLit d -> d.value().toPlainString() + "m";
            case Ast.StringLit s -> quoted(s.value());
            case Ast.BoolLit b -> Boolean.toString(b.value());
            case Ast.Neg n -> wrap("-", termKey(n.operand(), site, bound, depth));
            case Ast.Binary b -> {
                String l = termKey(b.left(), site, bound, depth);
                String r = termKey(b.right(), site, bound, depth);
                yield l == null || r == null ? null : "(" + l + " " + b.op() + " " + r + ")";
            }
            case Ast.ListLit l -> elementsKey("[", l.elements(), site, bound, depth, "]");
            case Ast.Tuple t -> elementsKey("(", t.elements(), site, bound, depth, ")");
            case Ast.TupleGet g -> wrap("." + g.index(), termKey(g.tuple(), site, bound, depth));
            case Ast.If iff -> elementsKey("if(", List.of(iff.cond(), iff.then(), iff.els()),
                    site, bound, depth, ")");
            case Ast.Block b -> {
                Map<String, String> inner = binding(bound, b.params(), depth);
                yield wrap("\\" + b.params().size(), termKey(b.body(), site, inner, depth + 1));
            }
            case Ast.LetIn li -> {
                String value = termKey(li.value(), site, bound, depth);
                Map<String, String> inner = binding(bound, List.of(li.name()), depth);
                String body = termKey(li.body(), site, inner, depth + 1);
                yield value == null || body == null ? null : "let(" + value + ", " + body + ")";
            }
            // Only the library's own functions: they are pure, so one written call is one value.
            case Ast.Call c when Prelude.hasQualified(c.fn()) ->
                    elementsKey(c.fn() + "(", c.args(), site, bound, depth, ")");
            default -> null;
        };
    }

    /** {@code bound} with each of {@code names} keyed by where it is bound rather than by its
     * spelling, so two expressions that differ only in what they called a binding are one term. */
    private static Map<String, String> binding(Map<String, String> bound, List<String> names, int depth) {
        Map<String, String> inner = new HashMap<>(bound);
        for (int i = 0; i < names.size(); i++) {
            inner.put(names.get(i), "#" + depth + "." + i);
        }
        return inner;
    }

    private String elementsKey(String open, List<Ast.Expr> parts, Function<Ast.Expr, String> site,
                               Map<String, String> bound, int depth, String close) {
        StringBuilder sb = new StringBuilder(open);
        for (int i = 0; i < parts.size(); i++) {
            String part = termKey(parts.get(i), site, bound, depth);
            if (part == null) {
                return null;
            }
            sb.append(i == 0 ? "" : ", ").append(part);
        }
        return sb.append(close).toString();
    }

    /** A string value written into a key with the punctuation the key itself uses escaped, so a value
     * holding a quote or a comma cannot be read back as a different expression. */
    private static String quoted(String value) {
        return "\"" + value.replace("\\", "\\\\").replace("\"", "\\\"") + "\"";
    }

    private static String wrap(String prefix, String inner) {
        return inner == null ? null : prefix + "(" + inner + ")";
    }

    /** The name at the head of a {@code x}/{@code x.a.b} chain, or {@code null} if {@code e} is not one. */
    private static String rootName(Ast.Expr e) {
        return switch (e) {
            case Ast.Var v -> v.name();
            case Ast.FieldAccess fa -> rootName(fa.target());
            default -> null;
        };
    }

    /** The field chain of {@code e} rebuilt on {@code head}. */
    private static String chainOn(String head, Ast.Expr e) {
        return e instanceof Ast.FieldAccess fa ? chainOn(head, fa.target()) + "." + fa.field() : head;
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

    /** What is known after a binding takes over {@code name}: everything that mentioned it is dropped,
     * because the name now denotes something else. The test is on the key's text and errs towards
     * dropping — a term that merely reads like it mentions the name loses a fact it could have kept,
     * which costs precision and never soundness. */
    private static Known rebind(Known k, String name) {
        return k.forgetIf(key -> mentions(key, name));
    }

    /** Whether {@code key} contains {@code name} as a whole identifier. */
    private static boolean mentions(String key, String name) {
        for (int i = key.indexOf(name); i >= 0; i = key.indexOf(name, i + 1)) {
            int end = i + name.length();
            boolean left = i == 0 || !Character.isUnicodeIdentifierPart(key.charAt(i - 1));
            boolean right = end == key.length() || !Character.isUnicodeIdentifierPart(key.charAt(end));
            if (left && right) {
                return true;
            }
        }
        return false;
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
