package souther.compiler.check;

import souther.compiler.Prelude;
import souther.compiler.ast.Ast;
import souther.compiler.diag.CompileException;
import souther.compiler.types.BindingId;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.function.Predicate;

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
            body = inliner.inline(h.written(), inliner.bodyOf(h.name()));
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
        return new Ast.FnDef(h.name(), params, h.declaredReturn(), h.body(),
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
        Type answers = declaredReturn(h, symbols);
        Map<Integer, Type> found = new LinkedHashMap<>();
        List<Integer> value = new ArrayList<>();
        for (int idx : open) {
            // a function-typed parameter is annotated, not settled (spec 13.1); reading a value type
            // off one would hide the report that says so.
            if (!isApplied(body, h.params().get(idx).binder())) {
                value.add(idx);
            }
        }
        boolean progress = true;
        while (progress) {
            progress = false;
            for (int idx : value) {
                Ast.Binder param = h.params().get(idx).binder();
                if (env.holds(param.id())) {
                    continue;
                }
                Type t = typing.typeOf(param, body, env, answers);
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
     * Whether {@code param} is applied in {@code e} — the shape only a function parameter has.
     */
    static boolean isApplied(Ast.Expr e, Ast.Binder param) {
        BindingId id = param.id();
        return exists(e, x -> x instanceof Ast.Apply call && refersTo(call.function(), id));
    }

    /** Whether {@code e} holds a use of {@code param} anywhere inside it. */
    static boolean mentions(Ast.Expr e, Ast.Binder param) {
        return mentions(e, param.id());
    }

    private static boolean mentions(Ast.Expr e, BindingId id) {
        return exists(e, x -> refersTo(x, id));
    }

    /**
     * Whether {@code e} is a use of the binding {@code id} — the binding it is, not the name it was
     * written with (ADR-0067). A binder that rebinds the name introduces another binding, so a
     * same-named lambda parameter, {@code let} or arm binding answers no without a walk that has to
     * know which node kinds bind: what the name resolved to already says it.
     */
    private static boolean refersTo(Ast.Expr e, BindingId id) {
        return e instanceof Ast.Var v && v.denotes() instanceof ValueName.Local local
                && local.id().equals(id);
    }

    /** Whether anything inside {@code e}, or {@code e} itself, satisfies {@code leaf}. */
    private static boolean exists(Ast.Expr e, Predicate<Ast.Expr> leaf) {
        if (leaf.test(e)) {
            return true;
        }
        boolean[] found = {false};
        TypeChecker.forEachChild(e, c -> {
            if (!found[0]) {
                found[0] = exists(c, leaf);
            }
        });
        return found[0];
    }

    /** The return type {@code h} declares, or null where it declares none or names something unknown. */
    private static Type declaredReturn(Ast.FnDef h, Symbols symbols) {
        if (h.declaredReturn() == null) {
            return null;
        }
        try {
            return TypeOps.successType(h.declaredReturn(), symbols);
        } catch (CompileException _) {
            return null;   // a return type that does not resolve; the check reports it
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

        /**
         * The type {@code body} gives {@code target}, or null when it gives none. {@code answers} is
         * what the body as a whole is asked for — the helper's declared return type, where it wrote
         * one — so a body that answers the parameter itself takes the type written beside it.
         */
        Type typeOf(Ast.Binder target, Ast.Expr body, Scope env, Type answers) {
            this.pinned = null;
            this.openUse = null;
            // A recursive helper's call is left standing rather than expanded, so the neighbouring
            // expression a parameter takes its type from can be one — `x + count(t)` reads `count(t)`
            // to type `x`. Its signature goes in here, once, and every inner scope is derived from
            // this one (spec 13.1). What is bound wins over it, as it does everywhere else.
            visit(body, env.reaching(recursiveHelperFns), target.id(), answers);
            return pinned;
        }

        /** A use of the parameter that named no type, from the last {@link #typeOf} that found none. */
        Ast.Var openUse() {
            return openUse;
        }

        /**
         * Reads {@code e} for the type it gives {@code target}. {@code expected} is what this position
         * is asked for, which every arm passes on in its own terms: an operand names it for the
         * operand beside it, an arm for its sibling arms, a call for its arguments. A use of the
         * parameter standing at a position that names a type is what settles it, so the same rule
         * answers a bare use, a use one arm down, and a use inside a construction.
         */
        private void visit(Ast.Expr e, Scope env, BindingId target, Type expected) {
            if (pinned != null || !mentions(e, target)) {
                return;
            }
            switch (e) {
                case Ast.Var v when refersTo(v, target) -> {
                    pin(expected);
                    if (pinned == null && openUse == null) {
                        openUse = v;   // a use of the parameter that no enclosing position typed
                    }
                    return;
                }
                case Ast.LetIn li -> {
                    visitLet(li, env, target, expected);
                    return;
                }
                case Ast.Binary bin -> {
                    Type both = bin.op() == Ast.BinOp.AND || bin.op() == Ast.BinOp.OR
                            ? Type.BOOL : null;
                    visitBeside(bin.left(), bin.right(), env, target, both);
                    visitBeside(bin.right(), bin.left(), env, target, both);
                    return;
                }
                case Ast.If iff -> {
                    visit(iff.cond(), env, target, Type.BOOL);
                    visitBeside(iff.then(), iff.els(), env, target, expected);
                    visitBeside(iff.els(), iff.then(), env, target, expected);
                    return;
                }
                case Ast.Match m -> {
                    visitMatch(m, env, target, expected);
                    return;
                }
                case Ast.ListLit list -> {
                    visitElements(list.elements(), env, target, expected);
                    return;
                }
                case Ast.Apply call -> {
                    visitArgs(call, env, target, expected);
                    return;
                }
                case Ast.NewData nd -> {
                    visitInits(nd, env, target);
                    return;
                }
                default -> { }
            }
            if (pinned != null) {
                return;
            }
            TypeChecker.forEachChild(e, c -> visit(c, env, target, null));
        }

        /**
         * Reads {@code e} for a position it shares with {@code sibling} — the two operands of an
         * operator, the two arms of an {@code if} — which is asked for {@code expected} where the
         * enclosing position states one and otherwise for whatever the sibling answers. The sibling is
         * typed only when {@code e} holds the parameter at all: typing a neighbour to answer a
         * question nothing in {@code e} asks is the walk's most expensive way of learning nothing.
         */
        private void visitBeside(Ast.Expr e, Ast.Expr sibling, Scope env, BindingId target,
                                 Type expected) {
            if (pinned != null || !mentions(e, target)) {
                return;
            }
            visit(e, env, target, settles(expected) ? expected : typed(sibling, env));
        }

        /**
         * A {@code let} demands a type of its value: the one written on it, or the callee's declared
         * parameter type, which the inliner carries onto the binding a helper call becomes. Where it
         * demands none, the constraint passes along the binding: {@code let y = x in y * 2} types
         * {@code x} through {@code y}, which is the shape a call to another body-typed helper inlines
         * to. A binding spelled like the parameter is another binding, and reads as one.
         */
        private void visitLet(Ast.LetIn li, Scope env, BindingId target, Type expected) {
            Type demanded = li.declaredType() == null ? null
                    : TypeOps.resolveParamType(li.declaredType(), symbols);
            if (isParam(li.value(), target)) {
                pin(demanded);
                if (pinned != null) {
                    return;
                }
                Ast.Var use = openUse;
                visit(li.body(), env, li.binder().id(), expected);   // the binding stands for the parameter
                openUse = use;                      // its uses are the binding's, not the parameter's
                if (pinned != null) {
                    return;
                }
            }
            visit(li.value(), env, target, demanded);
            if (pinned != null) {
                return;
            }
            visit(li.body(), bound(li, demanded, env), target, expected);
        }

        /**
         * {@code env} with what the binding is in force as. The written type says it, except where it
         * names a type variable: the binding a helper's expansion writes carries the callee's declared
         * type, so a combinator's {@code List<'a>} would stand in front of the {@code List<Int>} the
         * argument actually is. A variable names nothing (spec 13.1), so what the value is wins there.
         */
        private Scope bound(Ast.LetIn li, Type demanded, Scope env) {
            Type type = demanded;
            if (type == null || Type.mentions(type, x -> x instanceof Type.Var)) {
                Type value = carried(li, env);
                if (value != null) {
                    type = value;
                }
            }
            return type == null ? env : env.with(li.binder(), type);
        }

        /** The type a binding carries into its body, or null where this scope cannot type its value. */
        private Type carried(Ast.LetIn li, Scope env) {
            Type value = typed(li.value(), env);
            return value == null ? null : Elaborator.carriedType(li, value, symbols);
        }

        /**
         * The parameter standing where a sibling of it answers a value of the same type: an element
         * of a collection literal beside another element. The positions have one type, so the one
         * that names a type names the parameter's.
         */
        private void visitElements(List<Ast.Expr> elements, Scope env, BindingId target, Type expected) {
            if (elements.stream().noneMatch(e -> mentions(e, target))) {
                return;
            }
            Type element = expected instanceof Type.ListOf list && settles(list.element())
                    ? list.element() : sibling(elements, env, target);
            for (Ast.Expr e : elements) {
                visit(e, env, target, element);
                if (pinned != null) {
                    return;
                }
            }
        }

        /**
         * The type an element that does not hold the parameter answers — the elements share one type,
         * so one of them answering is the answer for all of them. An element holding the parameter is
         * not asked: this scope cannot type it, which is the question being worked out.
         */
        private Type sibling(List<Ast.Expr> elements, Scope env, BindingId target) {
            for (Ast.Expr e : elements) {
                if (!mentions(e, target)) {
                    Type t = typed(e, env);
                    if (t != null) {
                        return t;
                    }
                }
            }
            return null;
        }

        /**
         * Each arm of a {@code match}, asked for what the match as a whole is asked for and otherwise
         * for what a sibling arm answers — the arms have one type. An arm is read in a scope its own
         * binding is in force over, which is what the scrutinee's type gives: the case a named-sum arm
         * binds, or the element an {@code Option} arm unwraps.
         */
        private void visitMatch(Ast.Match m, Scope env, BindingId target, Type expected) {
            visit(m.scrutinee(), env, target, null);
            if (pinned != null || m.cases().stream().noneMatch(c -> holds(c, target))) {
                return;
            }
            Type scrutinee = typed(m.scrutinee(), env);
            Type answers = settles(expected) ? expected : siblingArm(m, env, target, scrutinee);
            for (Ast.Case c : m.cases()) {
                if (holds(c, target)) {
                    visit(c.body(), armScope(env, c, scrutinee), target, answers);
                    if (pinned != null) {
                        return;
                    }
                }
            }
        }

        /** Whether arm {@code c} reads the parameter. An arm binding a name spelled like it binds
         * another binding, whose uses are not the parameter's. */
        private boolean holds(Ast.Case c, BindingId target) {
            return mentions(c.body(), target);
        }

        /** The type an arm that does not hold the parameter answers — the arms share one type. */
        private Type siblingArm(Ast.Match m, Scope env, BindingId target, Type scrutinee) {
            for (Ast.Case c : m.cases()) {
                if (!holds(c, target)) {
                    Type t = typed(c.body(), armScope(env, c, scrutinee));
                    if (t != null) {
                        return t;
                    }
                }
            }
            return null;
        }

        /** {@code env} with what arm {@code c} binds, where the scrutinee's type says what that is. */
        private Scope armScope(Scope env, Ast.Case c, Type scrutinee) {
            if (c.binding() == null || c.caseTypes().size() != 1) {
                return env;
            }
            TypeName arm = c.caseTypes().get(0).denotes();
            Type bound = scrutinee instanceof Type.OptionOf opt && TypeName.SOME.equals(arm)
                    ? opt.element() : MatchElaborator.caseBindType(arm);
            return bound == null ? env : MatchElaborator.bound(env, c.binding(), bound);
        }

        /**
         * Each argument of a call, asked for the type the callee declares of that argument. Where the
         * declaration carries type variables, they are solved at this call first — from the arguments
         * that do not hold the parameter and from what the call as a whole is asked for — so a
         * parameter passed where a signature says {@code 'a} takes what {@code 'a} turned out to be.
         * Nothing is reported: a call the checker will refuse leaves the variables unsolved, and the
         * parameter stays as open as it was.
         */
        private void visitArgs(Ast.Apply call, Scope env, BindingId target, Type expected) {
            Type.FnOf sig = calleeSignature(call.reaches());
            List<Type> params = sig == null || sig.params().size() != call.args().size()
                    ? null : solved(call, sig, env, target, expected);
            for (int i = 0; i < call.args().size(); i++) {
                Type param = params == null ? null : params.get(i);
                Ast.Expr arg = call.args().get(i);
                if (arg instanceof Ast.Block lambda && param instanceof Type.FnOf step) {
                    visit(lambda.body(), walking(env, lambda, step), target, step.result());
                } else {
                    visit(arg, env, target, param);
                }
                if (pinned != null) {
                    return;
                }
            }
            visit(call.function(), env, target, null);
        }

        /**
         * The signature's variables that a closure argument settles. A combinator names its element only
         * through the closure it hands it to — nothing else in {@code List.map((v) -> v * 2, xs)} says
         * what {@code xs} holds — so the closure's parameters are read the way a helper's are, by the
         * same rule one step in. Only the positions its body determines are answered; the rest stay
         * the variables the signature wrote, which unify against anything.
         */
        private void solveFromClosure(Ast.Expr arg, Type.FnOf step, Scope env,
                                      Map<String, Type> bind, Ast.Apply call) {
            if (!(arg instanceof Ast.Block lambda)
                    || lambda.params().size() != step.params().size()) {
                return;
            }
            // What the arguments beside it have settled, as the closure sees it: its parameters are
            // in force over its body at those types, and its result is what the body is asked for.
            // `List.find((v) -> v, xs)` says the body answers a Bool, which is what settles `v` —
            // and `v` is the element, so it settles what `xs` holds.
            Type.FnOf known = TypeOps.substitute(step, bind) instanceof Type.FnOf f ? f : step;
            Scope inner = walking(env, lambda, known);
            for (int i = 0; i < lambda.params().size(); i++) {
                Type t = new BodyTyping(symbols, reqSigs, recursiveHelperFns)
                        .typeOf(lambda.params().get(i), lambda.body(), inner, known.result());
                if (t != null) {
                    // only a position the closure's body settled: unifying an undetermined one
                    // against the variable the signature wrote would bind that variable to itself
                    TypeOps.unify(step.params().get(i), t, bind, symbols, call.pos(), "closure");
                }
            }
        }

        /**
         * {@code env} with the lambda's own parameters bound to the types the call gives them. A
         * combinator says what it hands its closure — {@code List.map} over a {@code List<Int>} walks
         * Ints — so an operand beside the lambda's parameter is a value of known type, as it is
         * anywhere else. A parameter the call does not settle (an accumulator seeded with {@code []})
         * is left unbound rather than bound to a bottom nothing follows from.
         */
        private Scope walking(Scope env, Ast.Block lambda, Type.FnOf step) {
            Scope walked = env;
            for (int i = 0; i < lambda.params().size() && i < step.params().size(); i++) {
                Type t = step.params().get(i);
                if (settles(t)) {
                    walked = walked.with(lambda.params().get(i), t);
                }
            }
            return walked;
        }

        /** {@code sig}'s parameter types with the variables this call site settles substituted in. */
        private List<Type> solved(Ast.Apply call, Type.FnOf sig, Scope env, BindingId target,
                                  Type expected) {
            if (!Type.mentions(sig, x -> x instanceof Type.Var)) {
                return sig.params();
            }
            Map<String, Type> bind = new HashMap<>();
            try {
                if (settles(expected)) {
                    // tolerantly: a result that does not fit leaves what the arguments settled
                    // standing, as it does where a call is typed for real
                    BottomInfer.pinResultTypeVars(sig.result(), expected, bind, symbols, call.pos(),
                            "result of " + call.written());
                }
                // The stages `CallElaborator.applySignature` types a call in, in that order and
                // for its reason: an argument that is not a closure binds the variables, and the
                // closure is read against what they turned out to be — `List.fold((acc, x) -> acc + x,
                // 0, xs)` reads its step knowing the seed said `acc` is an Int.
                for (int i = 0; i < call.args().size(); i++) {
                    Ast.Expr arg = call.args().get(i);
                    Type param = sig.params().get(i);
                    if (param instanceof Type.FnOf || mentions(arg, target)) {
                        continue;   // a closure waits for the stage below; this argument is the one
                    }               // being typed, and typing it is the question being worked out
                    Type actual = typed(arg, env);
                    if (actual != null) {
                        TypeOps.unify(param, actual, bind, symbols, call.pos(), "argument");
                    }
                }
                for (int i = 0; i < call.args().size(); i++) {
                    Ast.Expr arg = call.args().get(i);
                    if (sig.params().get(i) instanceof Type.FnOf step && !mentions(arg, target)) {
                        solveFromClosure(arg, step, env, bind, call);
                    }
                }
            } catch (CompileException _) {
                return sig.params();   // the call does not fit its signature; the check reports it
            }
            List<Type> out = new ArrayList<>();
            for (Type param : sig.params()) {
                out.add(TypeOps.substitute(param, bind));
            }
            return out;
        }

        /** Each field of a construction, asked for the type that field holds. */
        private void visitInits(Ast.NewData nd, Scope env, BindingId target) {
            Ast.Data data = symbols.get(nd.typeName().denotes()) instanceof Ast.Data d ? d : null;
            for (Ast.FieldInit init : nd.inits()) {
                visit(init.value(), env, target,
                        data == null ? null : TypeOps.fieldType(data, init.name(), symbols));
                if (pinned != null) {
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
        private Type.FnOf calleeSignature(String fn) {
            ReqSig req = reqSigs.get(fn);
            if (req != null) {
                return new Type.FnOf(req.params(), req.success());
            }
            if (recursiveHelperFns.get(fn) instanceof Type.FnOf sig) {
                return sig;
            }
            // Only a kernel's signature: a Souther-bodied library callee here is a recursive
            // helper, and those are answered above with the types their call site instantiated.
            Prelude.PreludeEntry entry = Prelude.entry(fn);
            if (entry == null || !(entry.declaration().body() instanceof Ast.FnBody.Intrinsic)) {
                return null;
            }
            return new Type.FnOf(entry.signature().params(), entry.signature().result());
        }

        private boolean isParam(Ast.Expr e, BindingId target) {
            return refersTo(e, target);
        }

        /** {@code t} taken as the parameter's type, unless {@link #settles} says it states none. */
        private void pin(Type t) {
            if (settles(t)) {
                pinned = t;
            }
        }

        /**
         * Whether {@code t} is a type the parameter can take: not a function type (which must be
         * written), not a signature's type variable, and not one that answers no value — the bottom
         * an empty collection carries, the {@code Never} an {@code unreachable} arm answers with, the
         * type a reported error stands in for. Each of those leaves the parameter as open as it was:
         * an arm determines its sibling only where it answers a value (ADR-0066), and `Never` is
         * exactly the arm that answers none.
         */
        private boolean settles(Type t) {
            return t != null && !(t instanceof Type.FnOf)
                    && !Type.mentions(t, x -> x instanceof Type.Var)
                    && !Type.mentions(t, BottomInfer::answersNoValue);
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
