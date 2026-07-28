package souther.compiler.check;

import souther.compiler.Prelude;
import souther.compiler.ast.Ast;
import souther.compiler.core.Core;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Typing for {@code let} helpers: checking each one standalone against its parameter types, taking
 * the parameters that were left unwritten from the helper's own body, and working out what the
 * recursive ones construct.
 *
 * <p>A helper is typed by its body and never by its callers (spec 13.1, issue #176), so what a
 * helper means is settled by reading the helper. A non-recursive helper is inlined into its caller,
 * so most of its checking happens there; what is here is what only makes sense about the helper on
 * its own.
 */
public final class HelperTyping {

    private HelperTyping() {}

    /**
     * Type-checks every helper fn standalone against its own declared parameter types (spec 13.1).
     * Calls to other helpers in the body are expanded first, so what is left is builtins and
     * injected behaviors, which {@code reqSigs} resolves. The construction-permission and
     * {@code requires} checks are the caller's (the helper is inlined there), so they are not
     * repeated here.
     */
    static void checkHelpers(HelperInliner inliner, Symbols symbols,
                                     Map<String, ReqSig> reqSigs, Map<String, Type> recursiveHelperFns,
                                     Map<String, Ast.Expr> loweredBodies,
                                     TypeChecker.Elaborated elaborated) {
        for (Ast.FnDef h : inliner.helpers().values()) {
            boolean recursive = recursiveHelperFns.containsKey(h.name());
            Map<String, Type> env = new HashMap<>();
            List<Integer> inferred = new ArrayList<>();
            for (int i = 0; i < h.params().size(); i++) {
                Ast.FnParam p = h.params().get(i);
                Elaborator.rejectBuiltinShadow(p.name(), p.pos());
                if (p.type() == null) {
                    if (recursive) {
                        // a recursive helper is lowered to a method, not inlined, so no call site
                        // expands it — its parameter types cannot be inferred and must be declared.
                        throw CompileException.of(
                                Diagnostic.of(null, "check.helper.annotate").title("check.helper.title")
                                        .at(p.pos(), p.name().length()).args(h.name(), p.name()).build(),
                                "helper `let " + h.name() + "` must annotate parameter `" + p.name()
                                        + "` with its type (spec 13.1)");
                    }
                    // a parameter with no type beside it takes one from the body (spec 13.1).
                    inferred.add(i);
                    continue;
                }
                env.put(p.name(), TypeOps.resolveParamType(p.type(), symbols));
            }
            Elaborator.rejectBuiltinShadowing(h.body());
            // A recursive helper survives to the backend as a method on `$Fns`, so it is typed on the
            // body the Lower stage produced — the same tree the backend emits — and the Core this
            // check produces is what the backend emits from (issue #81). A non-recursive helper is
            // inlined at its call sites and never emitted on its own, so its standalone check expands
            // its body here; a recursive helper hides its own parameters from helper resolution while
            // that expansion runs (foldFrom's `step` is a parameter, not a same-named user helper).
            // Expanded once: the body an un-annotated parameter takes its type from is the same tree.
            Ast.Expr body = recursive
                    ? loweredBodies.get(h.name())
                    : inliner.inline(h.body());
            if (recursive && body == null) {
                // Lower keeps every recursive helper as a fn of the lowered module, and the backend
                // emits from that same list, so a recursive helper without a lowered body would leave
                // the backend a method to emit and no elaborated body to emit it from.
                throw new IllegalStateException(
                        "recursive helper `" + h.name() + "` has no lowered body");
            }
            if (!inferred.isEmpty()) {
                // Complete the env from the body, then run the same standalone check an annotated
                // helper gets — so a mis-declared return type or a mis-passed function argument in the
                // body is caught here, at the helper, not only where it is later inlined.
                typeFromBody(h, inferred, env, body, symbols, reqSigs, recursiveHelperFns);
            }
            // a helper that returns a function (e.g. `let adder (n) = (x) -> x + n`) has no application
            // here to infer the lambda's parameter types from; it is checked where it is inlined and
            // applied (spec §blocks).
            checkFunctionArgs(h.body(), env, symbols, reqSigs, inliner);
            if (Elaborator.producesFunction(body)) {
                continue;
            }
            if (recursiveHelperFns.containsKey(h.name())) {
                // a recursive helper is pure: it is a static method with no injected fields, so it
                // cannot reach an injected behavior — put the effect in the behavior that calls it.
                rejectInjectedCalls(body, h.name(), reqSigs.keySet());
            }
            // self- and mutual calls resolve through the helper signatures, so the recursion type-checks
            // without a fixpoint (each declares its return type, spec 13.1).
            Map<String, Type> tenv = new HashMap<>(env);
            tenv.putAll(recursiveHelperFns);
            // push a declared return type into the body so an empty-collection body (Map.empty(), [])
            // takes the declared element/value type rather than a bottom
            Type declaredReturn = h.declaredReturn() == null ? null : TypeOps.successType(h.declaredReturn(), symbols);
            Core elaboratedBody = Elaborator.elaborate(body, tenv, new CheckContext(symbols, null, reqSigs), declaredReturn);
            Type bodyType = elaboratedBody.type();
            if (recursive) {
                elaborated.helpers.put(h.name(), elaboratedBody);   // the backend emits this
            }
            // a declared return type — required on a recursive helper, allowed on any helper — must
            // match the body; a lying annotation is not silently ignored.
            if (declaredReturn != null) {
                Type declared = declaredReturn;
                if (!TypeOps.assignable(bodyType, declared, symbols)) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.helper.return").title("check.helper.title")
                                    .at(h.pos()).args(h.name(), Type.show(declared), Type.show(bodyType))
                                    .build(),
                            "helper `let " + h.name() + "` declares it returns " + declared
                                    + " but its body is " + bodyType);
                }
            }
        }
    }

    /**
     * Completes {@code env} with the type each un-annotated parameter takes from the helper's own
     * body (spec 13.1). A parameter whose type the body leaves open is annotated: Souther has no user
     * generics, so there is nothing to generalise an open parameter into, and the annotation is what
     * states the type instead.
     *
     * <p>A parameter a later round settles can settle an earlier one — {@code f(x, y)} where
     * {@code y}'s type follows from {@code x}'s — so the rounds run to a fixpoint. Failing that, the
     * report names the use that named no type.
     */
    private static void typeFromBody(Ast.FnDef h, List<Integer> open, Map<String, Type> env,
            Ast.Expr body, Symbols symbols, Map<String, ReqSig> reqSigs,
            Map<String, Type> recursiveHelperFns) {
        // A parameter used as a function is one, and neither applying it nor handing it to a
        // combinator determines its type; the inliner also needs the annotation to tell a function
        // parameter from a value one when it expands the call (spec 13.1). The expanded body is what
        // is read, so a parameter handed to `List.map` — applied inside the expansion rather than
        // where it is written — is reported as the function it is.
        for (int idx : open) {
            Ast.FnParam p = h.params().get(idx);
            if (isApplied(body, p.name())) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.helper.fnparam").title("check.helper.title")
                                .at(p.pos(), p.name().length()).args(h.name(), p.name()).build(),
                        "helper `let " + h.name() + "` parameter `" + p.name() + "` is used as a"
                                + " function; a function-typed parameter must be annotated with its"
                                + " type (spec 13.1)");
            }
        }
        BodyTyping typing = new BodyTyping(symbols, reqSigs, recursiveHelperFns);
        Map<Integer, Ast.Var> openUses = new HashMap<>();
        boolean progress = true;
        while (progress) {
            progress = false;
            for (int idx : open) {
                String name = h.params().get(idx).name();
                if (env.containsKey(name)) {
                    continue;
                }
                Type t = typing.typeOf(name, body, env);
                if (t == null) {
                    openUses.put(idx, typing.openUse());
                } else {
                    env.put(name, t);
                    progress = true;
                }
            }
        }
        for (int idx : open) {
            Ast.FnParam p = h.params().get(idx);
            if (env.containsKey(p.name())) {
                continue;
            }
            Diagnostic.Builder d = Diagnostic.of(null, "check.helper.infer").title("check.helper.title")
                    .at(p.pos(), p.name().length()).args(h.name(), p.name());
            if (openUses.get(idx) instanceof Ast.Var use) {
                d.secondary(Region.ofWidth(use.pos(), Elaborator.width(use)), "check.helper.infer.use");
            }
            throw CompileException.of(d.build(),
                    "helper `let " + h.name() + "` parameter `" + p.name() + "` is not determined by"
                            + " its body; annotate it with its type (spec 13.1)");
        }
    }

    /**
     * Whether {@code name} is applied in {@code e} — the shape only a function parameter has. A
     * binding that rebinds the name hides its body: an inner {@code let f = (x) -> ...} applied there
     * is not this parameter. ({@link #collectCalls} answers the same question for the recursive-helper
     * call graph, where the names are helper names rather than a local, so it does not follow scopes.)
     */
    private static boolean isApplied(Ast.Expr e, String name) {
        if (e instanceof Ast.Call call && call.fn().equals(name)) {
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
    private static void forEachInScope(Ast.Expr e, String name, java.util.function.Consumer<Ast.Expr> f) {
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
        Type typeOf(String name, Ast.Expr body, Map<String, Type> env) {
            this.pinned = null;
            this.openUse = null;
            visit(body, env, name);
            return pinned;
        }

        /** A use of the parameter that named no type, from the last {@link #typeOf} that found none. */
        Ast.Var openUse() {
            return openUse;
        }

        private void visit(Ast.Expr e, Map<String, Type> env, String name) {
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
                case Ast.Call call -> pinFromCall(call, name);
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
        private void visitLet(Ast.LetIn li, Map<String, Type> env, String name) {
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
            Map<String, Type> inner = env;
            if (bound != null) {
                inner = new HashMap<>(env);
                inner.put(li.name(), bound);
            }
            visit(li.body(), inner, name);
        }

        /** The type a binding carries into its body, or null where this scope cannot type its value. */
        private Type carried(Ast.LetIn li, Map<String, Type> env) {
            Type value = typed(li.value(), env);
            return value == null ? null : Elaborator.carriedType(li, value, symbols);
        }

        /** The parameter passed where a callee declares the type of that argument. */
        private void pinFromCall(Ast.Call call, String name) {
            List<Type> params = calleeParams(call.fn());
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
        private void pinFromInits(String typeName, List<Ast.FieldInit> inits, String name) {
            if (!(symbols.declaration(typeName) instanceof Ast.Data data)) {
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
            if (t == null || t instanceof Type.FnOf || isOpen(t)
                    || Type.mentions(t, BottomInfer::isBottom)) {
                return;
            }
            pinned = t;
        }

        /** The type of a neighbouring expression, or null where this scope cannot type it. */
        private Type typed(Ast.Expr e, Map<String, Type> env) {
            try {
                return Elaborator.typeOf(e, env, ctx);
            } catch (CompileException _) {
                return null;
            }
        }
    }

    /**
     * Signatures of the module's recursive helpers, each a {@link Type.FnOf} from its declared
     * parameter types to its declared return type. A recursive helper must declare its return type:
     * the type can't be inferred through the cycle. Registered in a body's environment so a self- or
     * mutual call type-checks (spec 13.1).
     */
    static Map<String, Type> recursiveHelperSigs(HelperInliner inliner, Symbols symbols) {
        Map<String, Type> sigs = new HashMap<>();
        for (String name : inliner.recursiveHelpers()) {
            Ast.FnDef h = inliner.helper(name);
            if (h.declaredReturn() == null) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.rechelper.return").title("check.helper.title")
                                .at(h.pos()).args(name).build(),
                        "recursive helper `let " + name + "` must declare its return type — `let " + name
                                + " (...) : <type> = ...` — because its result cannot be inferred through"
                                + " the recursion (spec 13.1)");
            }
            List<Type> params = new ArrayList<>();
            for (Ast.FnParam p : h.params()) {
                if (p.type() == null) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.helper.annotate").title("check.helper.title")
                                    .at(p.pos(), p.name().length()).args(name, p.name()).build(),
                            "helper `let " + name + "` must annotate parameter `" + p.name()
                                    + "` with its type (spec 13.1)");
                }
                // a recursive helper is a static method taking its parameters as values; a function
                // parameter is passed as a first-class Fn (a closure), applied inside the method.
                params.add(TypeOps.resolveParamType(p.type(), symbols));
            }
            sigs.put(name, Type.fn(params, TypeOps.successType(h.declaredReturn(), symbols)));
        }
        return sigs;
    }

    /** Rejects a call to a {@code partial} helper inside an invariant: an invariant is checked on every
     * construction and must terminate, so it may not call a helper that disclaims totality (spec
     * §invariant-expressions). A total helper — including the stdlib fold behind the list
     * quantifiers — is admissible and not in {@code partial}. */
    static void rejectPartialHelperInInvariant(Ast.Expr e, String data, Set<String> partial) {
        if (e instanceof Ast.Call call && partial.contains(call.fn())) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.invariant.partial").title("check.invariant.invalid.title")
                            .at(call.pos(), call.fn().length()).args(data, call.fn()).build(),
                    "the invariant of `" + data + "` calls the `partial` helper `" + call.fn()
                            + "`, which may not terminate; an invariant is checked at construction time"
                            + " and must terminate, so only a total helper may appear in it");
        }
        TypeChecker.forEachChild(e, c -> rejectPartialHelperInInvariant(c, data, partial));
    }

    /** Rejects a data construction inside an invariant: an invariant is pure — it observes the value
     * being built, it does not build another (spec §invariant-expressions, "Forbidden: data
     * construction"). Walks the inlined invariant, so a construction smuggled through a quantifier's
     * closure (e.g. {@code List.all(x -> Made { ... }.ok, xs)}) is caught too. */
    static void rejectConstructionInInvariant(Ast.Expr e, String data) {
        if (e instanceof Ast.NewData nd) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.invariant.construct").title("check.invariant.invalid.title")
                            .at(nd.pos(), nd.typeName().length()).args(data, nd.typeName()).build(),
                    "the invariant of `" + data + "` constructs `" + nd.typeName()
                            + "`, but an invariant may not construct a data — it observes the value being"
                            + " built, it does not build another (spec §invariant-expressions)");
        }
        TypeChecker.forEachChild(e, c -> rejectConstructionInInvariant(c, data));
    }

    /** Rejects a call to an injected behavior inside a recursive helper: it is pure (spec 13.1). */
    private static void rejectInjectedCalls(Ast.Expr e, String helper, Set<String> injected) {
        if (e instanceof Ast.Call call && injected.contains(call.fn())) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.rechelper.pure").title("check.helper.title")
                            .at(call.pos(), call.fn().length()).args(helper, call.fn()).build(),
                    "recursive helper `let " + helper + "` is pure and cannot call the injected behavior `"
                            + call.fn() + "` — put the effect in the behavior that calls this helper"
                            + " (spec 13.1)");
        }
        TypeChecker.forEachChild(e, c -> rejectInjectedCalls(c, helper, injected));
    }

    /**
     * Checks each function passed to a helper's function-typed parameter against that parameter's
     * declared type, at the call site — before the helper is expanded inline. Without this, a bad
     * function argument to a combinator surfaces deep inside the {@code fold} it derives from (a
     * non-{@code Bool} {@code filter} predicate as the {@code if} the derivation expands to), which
     * names the derivation, not the mistake. Here the error names the parameter and the combinator.
     *
     * <p>It walks the un-inlined body. Every helper call binds its signature's type variables from
     * its collection arguments ({@code 'a} from a {@code List<'a>}), then checks each function
     * argument against the resulting concrete function type. The check is best-effort: when an
     * argument's type cannot be determined in the available scope (a value bound further out), it is
     * skipped and the ordinary inlined check still applies.
     */
    static void checkFunctionArgs(Ast.Expr e, Map<String, Type> env, Symbols symbols,
                                          Map<String, ReqSig> reqs, HelperInliner inliner) {
        if (e instanceof Ast.Call call) {
            checkHelperCallFnArgs(call, env, symbols, reqs, inliner);
        }
        TypeChecker.forEachChild(e, sub -> checkFunctionArgs(sub, env, symbols, reqs, inliner));
    }

    private static void checkHelperCallFnArgs(Ast.Call call, Map<String, Type> env, Symbols symbols,
                                              Map<String, ReqSig> reqs, HelperInliner inliner) {
        Ast.FnDef h = inliner.helper(call.fn());
        if (h == null || call.args().size() != h.params().size()) {
            return;   // not a helper, or an arity mismatch the inliner reports
        }
        List<Type> declared = new ArrayList<>();
        boolean hasFn = false;
        for (Ast.FnParam p : h.params()) {
            // an unannotated parameter takes its type from the helper's body (spec 13.1); it is never a
            // function parameter, so leave its slot null and treat it as a non-function argument here.
            Type pt = p.type() == null ? null : TypeOps.resolveParamType(p.type(), symbols);
            declared.add(pt);
            hasFn |= pt instanceof Type.FnOf;
        }
        if (!hasFn) {
            return;
        }
        // the collection (non-function) arguments bind the signature's type variables — `'a` from a
        // `List<'a>` collection — so the function parameters become concrete before the check.
        Map<String, Type> bind = new HashMap<>();
        for (int i = 0; i < declared.size(); i++) {
            if (declared.get(i) == null || declared.get(i) instanceof Type.FnOf) {
                continue;
            }
            try {
                Type at = Elaborator.typeOf(inliner.inline(call.args().get(i)), env, new CheckContext(symbols, null, reqs));
                TypeOps.unify(declared.get(i), at, bind, symbols, call.pos(), "argument " + (i + 1));
            } catch (CompileException _) {
                return;   // can't pin the types here; leave it to the inlined check
            }
        }
        for (int i = 0; i < declared.size(); i++) {
            if (declared.get(i) instanceof Type.FnOf fn0) {
                Type.FnOf want = (Type.FnOf) TypeOps.substitute(fn0, bind);
                if (carriesBottom(want)) {
                    // An empty-collection seed ([], Map.empty) binds the accumulator to a bottom, and
                    // the step is what grows it to the concrete type — exactly the shape a fold over
                    // an empty seed has (`Map.fold(step, [], m)`). Nothing concrete to check against
                    // here; the inlined check, which sees the expected type pushed down, decides.
                    continue;
                }
                checkFunctionArg(h, h.params().get(i).name(), want,
                        call.args().get(i), env, symbols, reqs, inliner, bind);
            }
        }
    }

    /** Whether a step's signature still carries an empty-collection bottom in a parameter or in its
     * result — the accumulator of a fold seeded with {@code []} / {@code Map.empty()}, which only the
     * step itself grows to a concrete type. */
    private static boolean carriesBottom(Type.FnOf fn) {
        if (Type.mentions(fn.result(), BottomInfer::isBottom)) {
            return true;
        }
        for (Type p : fn.params()) {
            if (Type.mentions(p, BottomInfer::isBottom)) {
                return true;
            }
        }
        return false;
    }

    /** The block a combinator was handed answers with the wrong type, in written types on both sides
     * (`'b?` / `String`), not in the checker's own spelling. */
    private static CompileException blockReturnMismatch(Ast.FnDef h, String paramName, Type want,
                                                        Type got, SourcePos pos) {
        return CompileException.of(
                Diagnostic.of(null, "check.fn.blockparam.return").title("check.fn.title")
                        .at(pos).args(paramName, h.name(), Type.show(want), Type.show(got)).build(),
                "the block passed to `" + paramName + "` of `let " + h.name() + "` must return "
                        + Type.show(want) + " but returns " + Type.show(got));
    }

    /** Whether a type still holds a type variable, so nothing concrete can be checked against it yet.
     * A bare {@code 'b} is the common case (`map`'s result); a variable can also sit inside a
     * constructor — {@code filterMap}'s step answers {@code 'b?} — and that is just as open. */
    private static boolean isOpen(Type t) {
        return Type.mentions(t, x -> x instanceof Type.Var);
    }

    private static void checkFunctionArg(Ast.FnDef h, String paramName, Type.FnOf want, Ast.Expr arg,
                                         Map<String, Type> env, Symbols symbols,
                                         Map<String, ReqSig> reqs, HelperInliner inliner,
                                         Map<String, Type> bind) {
        if (arg instanceof Ast.Block lambda) {
            if (lambda.params().size() != want.params().size()) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.fn.blockparam.arity").title("check.fn.title")
                                .at(arg.pos()).args(paramName, h.name(), want.params().size(),
                                        lambda.params().size()).build(),
                        "the block passed to `" + paramName + "` of `let " + h.name() + "` takes "
                                + want.params().size() + " argument(s) but is written with "
                                + lambda.params().size());
            }
            Map<String, Type> lenv = new HashMap<>(env);
            for (int j = 0; j < lambda.params().size(); j++) {
                if (isOpen(want.params().get(j))) {
                    return;   // the parameter type is still open; nothing concrete to check
                }
                lenv.put(lambda.params().get(j), want.params().get(j));
            }
            Type got;
            try {
                got = Elaborator.typeOf(inliner.inline(lambda.body()), lenv, new CheckContext(symbols, null, reqs));
            } catch (CompileException _) {
                return;   // best-effort; the inlined check reports a genuine error with full context
            }
            if (isOpen(want.result())) {
                // The declared result still has a variable in it, so the shape around the variable is
                // what there is to check: `'b?` accepts a block answering with an optional and rejects
                // one answering with a plain value. Unifying also pins `'b` for the arguments after
                // this one. A failure is reported as the mismatch it is, in written types.
                try {
                    TypeOps.unify(want.result(), got, bind, symbols, lambda.pos(), "block result");
                } catch (CompileException _) {
                    throw blockReturnMismatch(h, paramName, want.result(), got, lambda.pos());
                }
                return;
            }
            if (!TypeOps.assignable(got, want.result(), symbols)) {
                throw blockReturnMismatch(h, paramName, want.result(), got, lambda.pos());
            }
        } else if (arg instanceof Ast.Var v && env.get(v.name()) instanceof Type vt && !(vt instanceof Type.FnOf)) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.fn.notfunction").title("check.fn.title")
                            .at(arg.pos()).args(paramName, h.name(), v.name()).build(),
                    "`" + paramName + "` of `let " + h.name() + "` expects a function, but `" + v.name()
                            + "` is a value, not a function");
        }
    }

    /**
     * The data each recursive helper constructs, transitively. A recursive helper is lowered to a
     * method rather than inlined, so its constructions do not appear in a caller's body; this map lets
     * {@link #collectConstructs} attribute them to the behavior that calls the helper (spec 12.5). The
     * closure follows recursive-helper calls: a helper's set includes what the recursive helpers it
     * calls construct. Non-recursive helper calls are already inlined into the bodies here.
     */
    static Map<String, Set<String>> recursiveHelperConstructs(
            Set<String> recursive, Map<String, Ast.Expr> loweredBodies,
            HelperInliner inliner, Symbols symbols) {
        Map<String, Set<String>> own = new HashMap<>();
        Map<String, Set<String>> calls = new HashMap<>();
        for (String h : recursive) {
            Ast.Expr body = loweredBodies.get(h);
            Set<String> bound = new HashSet<>();
            for (Ast.FnParam p : inliner.helper(h).params()) {
                bound.add(p.name());
            }
            Set<String> c = new HashSet<>();
            DataChecker.collectConstructs(body, c, symbols, bound, Map.of());   // recursive calls opaque here
            own.put(h, c);
            Set<String> callees = new LinkedHashSet<>();
            collectCalls(body, callees, recursive);
            calls.put(h, callees);
        }
        Map<String, Set<String>> full = new HashMap<>();
        for (String h : recursive) {
            full.put(h, new HashSet<>(own.get(h)));
        }
        // fixpoint: propagate each callee's constructions until nothing new is added (handles mutual
        // recursion, whose call graph has cycles).
        boolean changed = true;
        while (changed) {
            changed = false;
            for (String h : recursive) {
                for (String g : calls.get(h)) {
                    if (full.get(h).addAll(full.get(g))) {
                        changed = true;
                    }
                }
            }
        }
        return full;
    }

    /** Collects the names in {@code names} that {@code e} calls (a recursive-helper call graph edge). */
    private static void collectCalls(Ast.Expr e, Set<String> out, Set<String> names) {
        if (e instanceof Ast.Call call && names.contains(call.fn())) {
            out.add(call.fn());
        }
        TypeChecker.forEachChild(e, c -> collectCalls(c, out, names));
    }

}
