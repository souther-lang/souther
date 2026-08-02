package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.core.Core;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.Type;
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
     * {@code depends on} checks are the caller's (the helper is inlined there), so they are not
     * repeated here.
     */
    static void checkHelpers(HelperInliner inliner, Symbols symbols,
                                     Map<String, ReqSig> reqSigs, Map<String, Type> recursiveHelperFns,
                                     Map<String, Ast.Expr> loweredBodies,
                                     TypeChecker.Elaborated elaborated) {
        for (Ast.FnDef h : inliner.helpers().values()) {
            boolean recursive = recursiveHelperFns.containsKey(h.name());
            Scope env = Scope.NONE;
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
                env = env.with(p.binder(), TypeOps.resolveParamType(p.type(), symbols));
            }
            Elaborator.rejectBuiltinShadowing(h.body());
            // A helper the lowered module carries is one the backend emits — a recursive one, and one
            // an example row applies (ADR-0077) — so it is typed on the tree the backend emits from,
            // and the Core this check produces is what is emitted (issue #81). One that is only
            // inlined at its call sites has no body down there, so its standalone check expands its
            // body here; a recursive helper hides its own parameters from helper resolution while that
            // expansion runs (foldFrom's `step` is a parameter, not a same-named user helper).
            // Expanded once: the body an un-annotated parameter takes its type from is the same tree.
            Ast.Expr emitted = loweredBodies.get(h.name());
            Ast.Expr body = emitted != null ? emitted : inliner.inline(h.body(), inliner.bodyOf(h.name()));
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
            // A recursive helper is lowered to a method, so a self- or mutual call is left standing
            // rather than expanded; its signature is what a call to it is typed against, so it goes
            // into the environment before anything reads the body (spec 13.1). Every reader of the
            // body needs it, not just the elaboration below: a call to a method-lowered helper can sit
            // in a lambda handed to a combinator, and the check of that lambda reads the environment
            // it is given. A parameter of the same name wins: a binding in force wins over the
            // declaration it shadows (spec §fn-rules), so `let use (depth: Int)` reads its `depth` as
            // the Int it declares and not as the helper it is spelled like.
            Scope tenv = env.reaching(recursiveHelperFns);
            // a helper that returns a function (e.g. `let adder (n) = (x) -> x + n`) has no application
            // here to infer the lambda's parameter types from; it is checked where it is inlined and
            // applied (spec §blocks).
            checkFunctionArgs(h.body(), tenv, symbols, reqSigs, inliner);
            if (Elaborator.producesFunction(body)) {
                continue;
            }

            if (recursiveHelperFns.containsKey(h.name())) {
                // a recursive helper is pure: it is a static method with no injected fields, so it
                // cannot reach an injected behavior — put the effect in the behavior that calls it.
                rejectInjectedCalls(body, h.name(), reqSigs.keySet());
            }
            // push a declared return type into the body so an empty-collection body (Map.empty, [])
            // takes the declared element/value type rather than a bottom
            Type declaredReturn = h.declaredReturn() == null ? null : TypeOps.successType(h.declaredReturn(), symbols);
            Core elaboratedBody = Elaborator.elaborate(body, tenv, new CheckContext(symbols, null, reqSigs), declaredReturn);
            Type bodyType = elaboratedBody.type();
            elaborated.definitionTypes.put(h.name(), bodyType);
            if (emitted != null) {
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
     * <p>{@link HelperParams} settles these types before the module is lowered, and writes what it
     * settles back onto the parameter — so what reaches here open is what it could not settle. Reading
     * it again is what turns "not settled" into a report that names the use that named no type.
     */
    private static void typeFromBody(Ast.FnDef h, List<Integer> open, Scope env,
            Ast.Expr body, Symbols symbols, Map<String, ReqSig> reqSigs,
            Map<String, Type> recursiveHelperFns) {
        // A parameter used as a function is one, and neither applying it nor handing it to a
        // combinator determines its type; the inliner also needs the annotation to tell a function
        // parameter from a value one when it expands the call (spec 13.1). The expanded body is what
        // is read, so a parameter handed to `List.map` — applied inside the expansion rather than
        // where it is written — is reported as the function it is.
        for (int idx : open) {
            Ast.FnParam p = h.params().get(idx);
            if (HelperParams.isApplied(body, p.name())) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.helper.fnparam").title("check.helper.title")
                                .at(p.pos(), p.name().length()).args(h.name(), p.name()).build(),
                        "helper `let " + h.name() + "` parameter `" + p.name() + "` is used as a"
                                + " function; a function-typed parameter must be annotated with its"
                                + " type (spec 13.1)");
            }
        }
        Map<Integer, Ast.Var> openUses = new HashMap<>();
        HelperParams.determine(h, open, env, body, symbols, reqSigs, recursiveHelperFns, openUses);
        for (int idx : open) {
            Ast.FnParam p = h.params().get(idx);
            if (env.holds(p.binder().id())) {
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
        if (e instanceof Ast.Apply call && partial.contains(call.written())) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.invariant.partial").title("check.invariant.invalid.title")
                            .at(call.pos(), call.written().length()).args(data, call.written()).build(),
                    "the invariant of `" + data + "` calls the `partial` helper `" + call.written()
                            + "`, which may not terminate; an invariant is checked at construction time"
                            + " and must terminate, so only a total helper may appear in it");
        }
        TypeChecker.forEachChild(e, c -> rejectPartialHelperInInvariant(c, data, partial));
    }

    /**
     * Rejects a data construction inside one invariant clause: an invariant is pure — it observes the
     * value being built, it does not build another (spec §invariant-expressions, "Forbidden: data
     * construction"). Walks the inlined clause, so a construction smuggled through a quantifier's
     * closure (e.g. {@code List.all(x -> Made { ... }.ok, xs)}) is caught too, and so is one written
     * in a helper the clause names however many helpers away it is — the clause arrives here with
     * them expanded into it, carrying each construction at the position it was written.
     *
     * <p>That is also why the diagnostic carries two places. What is wrong is at the construction,
     * which may be in a helper that reads perfectly well on its own; what makes it wrong is the
     * clause that reaches it, which may be pages away. The clause is named as the second only when it
     * is somewhere else — a construction written in the clause itself has one place, and labelling it
     * twice says nothing.
     */
    static void rejectConstructionInInvariant(Ast.Expr e, String data, Ast.InvariantClause clause) {
        if (e instanceof Ast.NewData nd) {
            String constructed = nd.typeName().written();
            String named = clause.name().orElse(null);
            Diagnostic.Builder b = Diagnostic
                    .of(null, named == null ? "check.invariant.construct" : "check.invariant.construct.named")
                    .title("check.invariant.invalid.title")
                    .at(nd.pos(), constructed.length())
                    .args(data, constructed, named);
            if (nd.pos().line() != clause.pos().line()) {
                b.secondary(Region.point(clause.pos()),
                        named == null ? "check.invariant.construct.here.unnamed"
                                : "check.invariant.construct.here", named);
            }
            throw CompileException.of(b.build(),
                    "the invariant " + (named == null ? "" : "`" + named + "` ") + "of `" + data
                            + "` constructs `" + constructed
                            + "`, but an invariant may not construct a data — it observes the value being"
                            + " built, it does not build another (spec §invariant-expressions)");
        }
        TypeChecker.forEachChild(e, c -> rejectConstructionInInvariant(c, data, clause));
    }

    /**
     * Rejects an {@code unreachable} inside an invariant clause. An invariant answers whether the
     * value being built is admissible, and every path through it has to answer that; a path that
     * aborts instead would decide a construction by ending the computation, which is the invariant's
     * own abort taken for a reason the clause never stated (spec §invariant-expressions).
     *
     * <p>Walks the inlined clause, so one written in a helper the clause names is caught where it
     * was written, as a construction is.
     */
    static void rejectUnreachableInInvariant(Ast.Expr e, String data, Ast.InvariantClause clause) {
        if (e instanceof Ast.Unreachable u) {
            String named = clause.name().orElse(null);
            throw CompileException.of(
                    Diagnostic.of(null, "check.invariant.unreachable")
                            .title("check.invariant.invalid.title")
                            .at(u.pos(), "unreachable".length())
                            .args(data, named).build(),
                    "the invariant " + (named == null ? "" : "`" + named + "` ") + "of `" + data
                            + "` answers `unreachable`, but an invariant says whether the value holds"
                            + " on every path (spec §invariant-expressions)");
        }
        TypeChecker.forEachChild(e, c -> rejectUnreachableInInvariant(c, data, clause));
    }

    /** Rejects a call to an injected behavior inside a recursive helper: it is pure (spec 13.1). */
    private static void rejectInjectedCalls(Ast.Expr e, String helper, Set<String> injected) {
        if (e instanceof Ast.Apply call && injected.contains(call.written())) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.rechelper.pure").title("check.helper.title")
                            .at(call.pos(), call.written().length()).args(helper, call.written()).build(),
                    "recursive helper `let " + helper + "` is pure and cannot call the injected behavior `"
                            + call.written() + "` — put the effect in the behavior that calls this helper"
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
    static void checkFunctionArgs(Ast.Expr e, Scope env, Symbols symbols,
                                          Map<String, ReqSig> reqs, HelperInliner inliner) {
        if (e instanceof Ast.Apply call) {
            checkHelperCallFnArgs(call, env, symbols, reqs, inliner);
        }
        TypeChecker.forEachChild(e, sub -> checkFunctionArgs(sub, env, symbols, reqs, inliner));
    }

    private static void checkHelperCallFnArgs(Ast.Apply call, Scope env, Symbols symbols,
                                              Map<String, ReqSig> reqs, HelperInliner inliner) {
        // what the call applies, which a binding of a helper's spelling is not: applying a
        // function-typed parameter is not a call to the helper it happens to be named after
        Ast.FnDef h = inliner.applied(call);
        if (h == null || call.args().size() != h.params().size()) {
            return;   // applies no body, or an arity mismatch the inliner reports
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
                Type at = Elaborator.typeOf(inliner.inline(call.args().get(i), inliner.bodyOf(h.name())),
                        env, new CheckContext(symbols, null, reqs));
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
     * result — the accumulator of a fold seeded with {@code []} / {@code Map.empty}, which only the
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
                                         Scope env, Symbols symbols,
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
            Scope lenv = env;
            for (int j = 0; j < lambda.params().size(); j++) {
                if (isOpen(want.params().get(j))) {
                    return;   // the parameter type is still open; nothing concrete to check
                }
                lenv = lenv.with(lambda.params().get(j), want.params().get(j));
            }
            Type got;
            try {
                got = Elaborator.typeOf(inliner.inline(lambda.body(), inliner.bodyOf(h.name())), lenv,
                        new CheckContext(symbols, null, reqs));
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
        } else if (arg instanceof Ast.Var v
                && env.of(v.denotes(), v.name()) instanceof Type vt && !(vt instanceof Type.FnOf)) {
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
    static Map<String, DataChecker.Constructs> recursiveHelperConstructs(
            Set<String> recursive, Map<String, Ast.Expr> loweredBodies,
            HelperInliner inliner, Symbols symbols) {
        Map<String, DataChecker.Constructs> own = new HashMap<>();
        Map<String, Set<String>> calls = new HashMap<>();
        for (String h : recursive) {
            Ast.Expr body = loweredBodies.get(h);
            DataChecker.Constructs c = DataChecker.Constructs.empty();
            DataChecker.collectConstructs(body, c, symbols, Map.of());   // recursive calls opaque here
            own.put(h, c);
            Set<String> callees = new LinkedHashSet<>();
            collectCalls(body, callees, recursive);
            calls.put(h, callees);
        }
        Map<String, DataChecker.Constructs> full = new HashMap<>();
        for (String h : recursive) {
            full.put(h, own.get(h).copy());
        }
        // fixpoint: propagate each callee's constructions until nothing new is added (handles mutual
        // recursion, whose call graph has cycles). The two kinds travel apart the whole way: a
        // construction another module's published body carried into this helper is still that
        // module's where the behavior calling the helper reads it, and merging them here is how a
        // reader came to be told it declares a construction it does not make.
        boolean changed = true;
        while (changed) {
            changed = false;
            for (String h : recursive) {
                for (String g : calls.get(h)) {
                    changed |= full.get(h).absorb(full.get(g));
                }
            }
        }
        return full;
    }

    /** Collects the names in {@code names} that {@code e} calls (a recursive-helper call graph edge). */
    private static void collectCalls(Ast.Expr e, Set<String> out, Set<String> names) {
        if (e instanceof Ast.Apply call && names.contains(call.written())) {
            out.add(call.written());
        }
        TypeChecker.forEachChild(e, c -> collectCalls(c, out, names));
    }

}
