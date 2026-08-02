package souther.compiler.check;

import souther.compiler.Prelude;
import souther.compiler.ast.Ast;
import souther.compiler.diag.CompileException;
import souther.compiler.types.Type;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Settles the type of every helper parameter the author left unwritten, reading it off the helper's
 * own body (spec 13.1, issue #176) and writing it back onto the parameter (issue #178).
 *
 * <p>Writing it back is what makes the type reach the helper's expansion. A helper call is rewritten
 * to {@code let $k_p = arg in <body>} carrying the parameter's type onto the binding, so a value the
 * helper knows to be a sum is not narrowed to the case the caller passed when the body is re-checked
 * inline. That happens in {@link Lower}, before the type checker runs, so a type the checker settles
 * would arrive too late — the type is settled here instead, on the tree, and the inliner reads it
 * like any written one. The type is written as a reference with no surface text (see
 * {@link Ast.TypeRef#of}): what a parameter denotes is decided, and no source stands for it.
 *
 * <p>Settling is best-effort and reports nothing. A parameter its body does not determine is left as
 * it was, for {@link HelperTyping} to report where it reports today — so a helper that cannot be
 * typed still names the use that left it open, and one broken helper still does not hide the errors
 * in the rest of the module.
 */
final class HelperParams {

    private HelperParams() {}

    /**
     * {@code module} with each settleable helper parameter carrying the type its body gives it. One
     * helper's settled type can settle the next one's — {@code describe}'s parameter is determined
     * only by passing it to {@code hold}, whose own parameter the body settles — so the rounds run
     * until nothing new is settled.
     */
    static Ast.Module settle(Ast.Module module, Symbols symbols, Map<String, ReqSig> reqSigs) {
        Ast.Module current = module;
        while (true) {
            Ast.Module next = settleOnce(current, symbols, reqSigs);
            if (next == current) {
                return current;
            }
            current = next;
        }
    }

    /** One round: returns {@code m} itself when no parameter was settled. */
    private static Ast.Module settleOnce(Ast.Module m, Symbols symbols, Map<String, ReqSig> reqSigs) {
        if (!hasOpenParam(m)) {
            return m;   // nothing to settle: don't build the inliner (it scans the whole prelude)
        }
        HelperInliner inliner = HelperInliner.forModule(m);
        Set<String> recursive = inliner.recursiveHelpers();
        Map<String, Type> recursiveHelperFns;
        try {
            recursiveHelperFns = HelperTyping.recursiveHelperSigs(inliner, symbols);
        } catch (CompileException _) {
            // One recursive helper that does not declare its types costs the signatures of all of
            // them, which is not observable: the check builds this same map outside its recovery, so
            // the module is abandoned on that error before any helper is typed. If that map is ever
            // made recoverable, this has to be made per-helper along with it — otherwise a helper
            // this leaves unsettled is reported as undetermined on top of the real error.
            recursiveHelperFns = Map.of();
        }
        Map<String, Ast.FnDef> settled = new LinkedHashMap<>();
        for (Ast.FnDef h : inliner.helpers().values()) {
            if (recursive.contains(h.name())) {
                continue;   // a recursive helper is not inlined and declares its parameters (spec 13.1)
            }
            Ast.FnDef s = settle(h, inliner, symbols, reqSigs, recursiveHelperFns);
            if (s != null) {
                settled.put(h.name(), s);
            }
        }
        if (settled.isEmpty()) {
            return m;
        }
        List<Ast.FnDef> fns = new ArrayList<>();
        for (Ast.FnDef fn : m.fns()) {
            fns.add(settled.getOrDefault(fn.name(), fn));
        }
        return new Ast.Module(m.name(), m.exposing(), m.exposedOutputs(), m.imports(), m.defs(),
                m.behaviors(), fns, m.examples(), m.fakes(), m.exampleFileTarget(), m.pos());
    }

    /**
     * Whether {@code m} has a helper parameter with no type written on it — the only thing there is
     * to settle. A behavior's implementation is not a helper: its parameters are typed from the
     * behavior and carry no type of their own, so counting them would answer yes for every module
     * that implements a behavior and this would never skip anything.
     */
    private static boolean hasOpenParam(Ast.Module m) {
        Set<String> behaviors = new HashSet<>();
        for (Ast.BehaviorDef b : m.behaviors()) {
            behaviors.add(b.name());
        }
        for (Ast.FnDef fn : m.fns()) {
            if (behaviors.contains(fn.name())) {
                continue;
            }
            for (Ast.FnParam p : fn.params()) {
                if (p.type() == null) {
                    return true;
                }
            }
        }
        return false;
    }

    /** {@code h} with its determinable parameters typed, or null when none of them is. */
    private static Ast.FnDef settle(Ast.FnDef h, HelperInliner inliner, Symbols symbols,
                                    Map<String, ReqSig> reqSigs, Map<String, Type> recursiveHelperFns) {
        List<Integer> open = new ArrayList<>();
        Scope env = Scope.NONE;
        Ast.Expr body;
        try {
            for (int i = 0; i < h.params().size(); i++) {
                Ast.FnParam p = h.params().get(i);
                if (p.type() == null) {
                    open.add(i);
                } else {
                    env = env.with(p.binder(), TypeOps.resolveParamType(p.type(), symbols));
                }
            }
            if (open.isEmpty()) {
                return null;
            }
            body = inliner.inline(h.body(), inliner.bodyOf(h.name()));
        } catch (CompileException _) {
            return null;   // a written type or a call that does not resolve; the check reports it
        }
        Map<Integer, Type> found =
                determine(h, open, env, body, symbols, reqSigs, recursiveHelperFns, new HashMap<>());
        if (found.isEmpty()) {
            return null;
        }
        List<Ast.FnParam> params = new ArrayList<>();
        for (int i = 0; i < h.params().size(); i++) {
            Ast.FnParam p = h.params().get(i);
            Type t = found.get(i);
            params.add(t == null ? p
                    : new Ast.FnParam(p.binder(),
                            new Ast.RetType(List.of(Ast.TypeRef.of(t, p.pos())), p.pos()),
                            p.typeFromPattern()));
        }
        return new Ast.FnDef(h.name(), params, h.declaredReturn(), h.intrinsicKey(), h.body(),
                h.partial(), h.pos());
    }

    /**
     * The type {@code body} gives each of {@code open}, by index. A parameter a later round settles
     * can settle an earlier one — {@code f(x, y)} where {@code y}'s type follows from {@code x}'s —
     * so the rounds run to a fixpoint. {@code env} is completed as they are found, and
     * {@code openUses} collects, for each parameter still open, a use of it that named no type.
     */
    static Map<Integer, Type> determine(Ast.FnDef h, List<Integer> open, Scope env,
                                        Ast.Expr body, Symbols symbols, Map<String, ReqSig> reqSigs,
                                        Map<String, Type> recursiveHelperFns,
                                        Map<Integer, Ast.Var> openUses) {
        BodyTyping typing = new BodyTyping(symbols, reqSigs, recursiveHelperFns);
        Map<Integer, Type> found = new LinkedHashMap<>();
        List<Integer> value = new ArrayList<>();
        for (int idx : open) {
            // a function-typed parameter is annotated, not settled (spec 13.1); reading a value type
            // off one would hide the report that says so.
            if (!isApplied(body, h.params().get(idx).name())) {
                value.add(idx);
            }
        }
        boolean progress = true;
        while (progress) {
            progress = false;
            for (int idx : value) {
                Ast.Binder param = h.params().get(idx).binder();
                String name = param.name();
                if (env.holds(param.id())) {
                    continue;
                }
                Type t = typing.typeOf(name, body, env);
                if (t == null) {
                    openUses.put(idx, typing.openUse());
                } else {
                    env = env.with(param, t);
                    found.put(idx, t);
                    progress = true;
                }
            }
        }
        return found;
    }

    /**
     * Whether {@code name} is applied in {@code e} — the shape only a function parameter has. A
     * binding that rebinds the name hides its body: an inner {@code let f = (x) -> ...} applied there
     * is not this parameter.
     */
    static boolean isApplied(Ast.Expr e, String name) {
        if (e instanceof Ast.Apply call && call.written().equals(name)) {
            return true;
        }
        boolean[] found = {false};
        forEachInScope(e, name, c -> {
            if (!found[0]) {
                found[0] = isApplied(c, name);
            }
        });
        return found[0];
    }

    /**
     * Walks the children of {@code e} that {@code name} still means the parameter in. A binder that
     * rebinds the name — a {@code let}, a lambda parameter, a {@code match} arm's binding — hides
     * what it binds over, so a same-named local is not read as the parameter.
     */
    static void forEachInScope(Ast.Expr e, String name, java.util.function.Consumer<Ast.Expr> f) {
        switch (e) {
            case Ast.LetIn li -> {
                f.accept(li.value());
                if (!li.name().equals(name)) {
                    f.accept(li.body());
                }
            }
            case Ast.Block b -> {
                if (!b.params().contains(name)) {
                    f.accept(b.body());
                }
            }
            case Ast.Match m -> {
                f.accept(m.scrutinee());
                for (Ast.Case c : m.cases()) {
                    if (!name.equals(c.binding())) {
                        f.accept(c.body());
                    }
                }
            }
            default -> TypeChecker.forEachChild(e, f);
        }
    }

    /**
     * One parameter's type read out of the helper's body. The whole body is read, so a position after
     * a use that named no type still determines it; the order the body is written decides only which
     * of several determining positions wins.
     *
     * <p>It answers with a type or with nothing; it never reports a type error. A type the rest of the
     * body disagrees with is reported by the standalone check that follows, at the position of the
     * disagreement, so type errors keep coming from one place ({@link Elaborator}). Where nothing
     * names a type, {@link #openUse()} is a use that named none, for the report to point at.
     */
    private static final class BodyTyping {
        private final Symbols symbols;
        private final CheckContext ctx;
        private final Map<String, ReqSig> reqSigs;
        private final Map<String, Type> recursiveHelperFns;
        private Type pinned;
        private Ast.Var openUse;

        BodyTyping(Symbols symbols, Map<String, ReqSig> reqSigs, Map<String, Type> recursiveHelperFns) {
            this.symbols = symbols;
            this.ctx = new CheckContext(symbols, null, reqSigs);
            this.reqSigs = reqSigs;
            this.recursiveHelperFns = recursiveHelperFns;
        }

        /** The type {@code body} gives {@code name}, or null when it gives none. */
        Type typeOf(String name, Ast.Expr body, Scope env) {
            this.pinned = null;
            this.openUse = null;
            // A recursive helper's call is left standing rather than expanded, so the neighbouring
            // expression a parameter takes its type from can be one — `x + count(t)` reads `count(t)`
            // to type `x`. Its signature goes in here, once, and every inner scope is derived from
            // this one (spec 13.1). What is bound wins over it, as it does everywhere else.
            visit(body, env.reaching(recursiveHelperFns), name);
            return pinned;
        }

        /** A use of the parameter that named no type, from the last {@link #typeOf} that found none. */
        Ast.Var openUse() {
            return openUse;
        }

        private void visit(Ast.Expr e, Scope env, String name) {
            if (pinned != null) {
                return;
            }
            switch (e) {
                case Ast.LetIn li -> {
                    visitLet(li, env, name);
                    return;
                }
                case Ast.Binary bin -> {
                    if (bin.op() == Ast.BinOp.AND || bin.op() == Ast.BinOp.OR) {
                        if (isParam(bin.left(), name) || isParam(bin.right(), name)) {
                            pin(Type.BOOL);
                        }
                    } else if (isParam(bin.left(), name)) {
                        pin(typed(bin.right(), env));
                    } else if (isParam(bin.right(), name)) {
                        pin(typed(bin.left(), env));
                    }
                }
                case Ast.If iff -> {
                    if (isParam(iff.cond(), name)) {
                        pin(Type.BOOL);
                    }
                }
                case Ast.Apply call -> pinFromCall(call, name);
                case Ast.NewData nd -> pinFromInits(nd.typeName(), nd.inits(), name);
                case Ast.Var v when v.name().equals(name) -> {
                    if (openUse == null) {
                        openUse = v;   // a use of the parameter that no enclosing position typed
                    }
                }
                default -> { }
            }
            if (pinned != null) {
                return;
            }
            forEachInScope(e, name, c -> visit(c, env, name));
        }

        /**
         * A {@code let} demands a type of its value: the one written on it, or the callee's declared
         * parameter type, which the inliner carries onto the binding a helper call becomes. Where it
         * demands none, the constraint passes along the binding: {@code let y = x in y * 2} types
         * {@code x} through {@code y}, which is the shape a call to another body-typed helper inlines
         * to. A binding of the parameter's own name shadows it, so its body is not walked for it.
         */
        private void visitLet(Ast.LetIn li, Scope env, String name) {
            Type demanded = li.declaredType() == null ? null
                    : TypeOps.resolveParamType(li.declaredType(), symbols);
            if (isParam(li.value(), name)) {
                pin(demanded);
                if (pinned != null) {
                    return;
                }
                Ast.Var use = openUse;
                visit(li.body(), env, li.name());   // the binding stands for the parameter
                openUse = use;                      // its uses are the binding's, not the parameter's
                if (pinned != null) {
                    return;
                }
            }
            visit(li.value(), env, name);
            if (pinned != null || li.name().equals(name)) {
                return;
            }
            Type bound = demanded != null ? demanded : carried(li, env);
            visit(li.body(), bound == null ? env : env.with(li.binder(), bound), name);
        }

        /** The type a binding carries into its body, or null where this scope cannot type its value. */
        private Type carried(Ast.LetIn li, Scope env) {
            Type value = typed(li.value(), env);
            return value == null ? null : Elaborator.carriedType(li, value, symbols);
        }

        /** The parameter passed where a callee declares the type of that argument. */
        private void pinFromCall(Ast.Apply call, String name) {
            List<Type> params = calleeParams(call.written());
            if (params == null || params.size() != call.args().size()) {
                return;
            }
            for (int i = 0; i < call.args().size(); i++) {
                if (isParam(call.args().get(i), name)) {
                    pin(params.get(i));
                    return;
                }
            }
        }

        /** The parameter written as a field of a construction takes that field's type. */
        private void pinFromInits(Ast.Name typeName, List<Ast.FieldInit> inits, String name) {
            if (!(symbols.get(typeName.denotes()) instanceof Ast.Data data)) {
                return;
            }
            for (Ast.FieldInit init : inits) {
                if (isParam(init.value(), name)) {
                    pin(TypeOps.fieldType(data, init.name(), symbols));
                    return;
                }
            }
        }

        /**
         * The parameter types {@code fn} declares, or null when nothing here declares them. A helper
         * that annotates its parameters has already been inlined into this body, where its annotation
         * is on the binding the call became, and a newtype's constructor {@code X(v)} has already been
         * desugared to a construction; what is left to read is an injected behavior, a recursive
         * helper and an intrinsic. A built-in that is neither an intrinsic nor a self-hosted helper
         * states its parameter types only inside {@link CallElaborator}, so an argument of one is not
         * read here — the parameter is annotated instead.
         */
        private List<Type> calleeParams(String fn) {
            ReqSig req = reqSigs.get(fn);
            if (req != null) {
                return req.params();
            }
            if (recursiveHelperFns.get(fn) instanceof Type.FnOf sig) {
                return sig.params();
            }
            Prelude.IntrinsicSig intrinsic = Prelude.intrinsics().get(fn);
            return intrinsic == null ? null : intrinsic.params();
        }

        private boolean isParam(Ast.Expr e, String name) {
            return e instanceof Ast.Var v && v.name().equals(name);
        }

        /**
         * {@code t} taken as the parameter's type, unless it is one nothing concrete follows from: a
         * function type (which must be written), a signature's type variable, or the bottom an empty
         * collection carries — each of those leaves the parameter as open as it was.
         */
        private void pin(Type t) {
            if (t == null || t instanceof Type.FnOf || Type.mentions(t, x -> x instanceof Type.Var)
                    || Type.mentions(t, BottomInfer::isBottom)) {
                return;
            }
            pinned = t;
        }

        /** The type of a neighbouring expression, or null where this scope cannot type it. */
        private Type typed(Ast.Expr e, Scope env) {
            try {
                return Elaborator.typeOf(e, env, ctx);
            } catch (CompileException _) {
                return null;
            }
        }
    }
}
