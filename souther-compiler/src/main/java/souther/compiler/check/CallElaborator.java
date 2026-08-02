package souther.compiler.check;

import souther.compiler.Prelude;
import souther.compiler.ast.Ast;
import souther.compiler.core.Core;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Localizable;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.types.ValueName;
import java.util.Set;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;

/**
 * Typing a call: a builtin, a helper, an injected behavior, or a data construction. Resolves the
 * argument types, binds any type variables the callee declares, and picks the result from them.
 */
public final class CallElaborator {

    private CallElaborator() {}

    /** The members of a primitive-headed union — {@code Int | DivisionByZero} — the output of a
     * partial built-in. The head is a primitive case, and the error case is declared by the runtime
     * rather than by a module (see {@link TypeName#RUNTIME}). */
    /**
     * The kernels whose element must be an ordered value, and where in the result to find it.
     *
     * <p>Souther has no type classes, so "the element is ordered" is not something a signature can
     * say (ADR-0053). The declaration states the shape and this states the rest, keyed by the kernel
     * it constrains — which is what {@code sort} has always done, written out by hand.
     */
    /** Where the element whose order is required sits in a kernel's result. */
    private enum OrderedElement { OF_THE_LIST, OF_THE_OPTION }

    private static final Map<String, OrderedElement> ORDERED_ELEMENT = Map.of(
            "list.sort", OrderedElement.OF_THE_LIST,
            "list.max", OrderedElement.OF_THE_OPTION,
            "list.min", OrderedElement.OF_THE_OPTION);

    /**
     * Refuses an element with no natural order. An ordered primitive has one, and so does a newtype
     * over one — it carries its ordering as {@code Comparable}. A product data does not and would
     * throw at run time, so it is refused here. The empty-list literal (element {@code Nothing}) is
     * fine: it sorts to itself and its max is {@code None}.
     */
    private static void requiresOrdering(String key, Ast.Apply call, Type result, CheckContext ctx) {
        OrderedElement where = ORDERED_ELEMENT.get(key);
        if (where == null) {
            return;
        }
        boolean inOption = where == OrderedElement.OF_THE_OPTION;
        Type element = switch (result) {
            case Type.OptionOf o when inOption -> o.element();
            case Type.ListOf l when !inOption -> l.element();
            default -> null;
        };
        if (element == null || element instanceof Type.Nothing
                || TypeOps.supportsOrdering(element, ctx.symbols())) {
            return;
        }
        String name = call.written().substring(call.written().indexOf('.') + 1);
        throw needsOrdered(call.pos(), name, element,
                name + " needs a list of ordered values (Int, String, Decimal, Date, DateTime, a"
                        + " newtype over one of these, or an enumeration), but the element is "
                        + element + " — use its ordered field instead (e.g. map to it first)");
    }

    /** Whether a declared parameter takes a rounding mode rather than a value. */
    private static boolean isRoundingMode(Type t) {
        return t instanceof Type.Ref r && r.name().equals(TypeOps.ROUNDING_MODE);
    }

    /**
     * Refuses a sort key with no natural order. The constraint is on what the key answers, not on
     * what the list holds, so it reads the binding the key's declared result took rather than the
     * call's result.
     */
    private static void requiresOrderedKey(String key, Ast.Apply call, Type.FnOf declaredKey,
                                           Map<String, Type> bindings, CheckContext ctx) {
        if (!key.equals("list.sortBy")) {
            return;
        }
        Type answered = TypeOps.substitute(declaredKey.result(), bindings);
        if (BottomInfer.isBottom(answered) || answered instanceof Type.Var
                || TypeOps.supportsOrdering(answered, ctx.symbols())) {
            return;
        }
        throw CompileException.of(
                Diagnostic.of(null, "check.ordered.key").title("check.type.mismatch.title")
                        .at(call.pos()).args(call.written(), Type.show(answered))
                        .hint("check.ordered.hint").build(),
                call.written() + "'s key must be an ordered value (Int, String, Decimal, Date, DateTime,"
                        + " a newtype over one of these, or an enumeration), but returns " + answered);
    }

    /**
     * A library name written where a value goes, or null where the name is not a library value.
     *
     * <p>A declaration with no parameter list is a value ([#fn-declaration]), and the library's are
     * the two empty collections. Their type comes from the context the way {@code []}'s does: the
     * expected type pins what the declaration left open, and what it does not pin is the bottom that
     * a later position fixes (ADR-0028).
     *
     * <p>The Core is the one the application spelling produced, so nothing downstream of here tells
     * the two apart — which is what keeps a growing fold's seed the seed it was.
     */
    static Core libraryValue(Ast.Var v, CheckContext ctx, Type expected) {
        if (!(v.denotes() instanceof ValueName.Stdlib lib)) {
            return null;
        }
        Prelude.IntrinsicSig intrinsic = Prelude.intrinsics().get(lib.qualified());
        if (intrinsic == null || !intrinsic.params().isEmpty()) {
            return null;
        }
        Map<String, Type> bindings = new HashMap<>();
        BottomInfer.pinResultTypeVars(intrinsic.result(), expected, bindings, ctx.symbols(),
                v.pos(), "the type of " + lib.qualified());
        return new Core.Call(lib.qualified(), List.of(),
                TypeOps.toBottom(TypeOps.substitute(intrinsic.result(), bindings)), v.pos());
    }

    static Core elaborateCall(Ast.Apply call, Scope env, CheckContext ctx,
                                      Type expected) {
        CallArgs ca = new CallArgs(call.args(), env, ctx);
        Type result = typeOfCall(ca, call, env, ctx, expected);
        // applying something this body binds is a different operation from calling something
        // declared elsewhere, and it is the only one that carries a binding into the emitted tree
        if (call.denotes() instanceof ValueName.Local local
                && env.typeOf(local.id()) instanceof Type.FnOf) {
            return new Core.Apply(
                    new Core.Read(call.written(), local.id(), env.typeOf(local.id()), call.pos()),
                    ca.cores(), result, call.pos());
        }
        return new Core.Call(call.reaches(), ca.cores(), result, call.pos());
    }

    /**
     * The arguments of one call, each elaborated once, as the call's typing rule reaches it. A rule
     * types its arguments in its own order and shape — some through a required type, a step through
     * the accumulator the other arguments fixed — so the Core for each argument is collected here
     * rather than by a separate walk that would have to reconstruct that context.
     */
    static final class CallArgs {
        private final List<Ast.Expr> args;
        private final Core[] cores;
        private final Scope env;
        private final CheckContext ctx;

        CallArgs(List<Ast.Expr> args, Scope env, CheckContext ctx) {
            this.args = args;
            this.cores = new Core[args.size()];
            this.env = env;
            // An argument is not the value a `?` field is being given, whatever encloses the call, so
            // it does not make an optional (ADR-0011). An argument is also typed with no expected
            // type, which already refuses `None`; dropping the permission states the rule here rather
            // than leaving it to rest on that.
            this.ctx = ctx.makingAnOptional(false);
        }

        /** The type of argument {@code i}, elaborated with no expected type (bottom-up). */
        Type type(int i) {
            Core c = Elaborator.elaborate(args.get(i), env, ctx);
            cores[i] = c;
            return c.type();
        }

        /** Argument {@code i} checked against {@code expected}, as {@link #requireType} does. */
        void require(int i, Type expected, String what) {
            Core c = Elaborator.elaborate(args.get(i), env, ctx);
            cores[i] = c;
            Elaborator.requireType(args.get(i), c.type(), expected, ctx.symbols(), what);
        }

        /** Argument {@code i} as a block (or a function value standing in for one), returning the
         * result type the block yields at {@code paramTypes}. */
        Type block(int i, String fnName, List<Type> paramTypes) {
            Core c = Elaborator.elaborateBlockArg(fnName, args.get(i), paramTypes, env, ctx);
            cores[i] = c;
            return ((Type.FnOf) c.type()).result();
        }

        void put(int i, Core c) {
            cores[i] = c;
        }

        /** Records argument {@code i} as carrying no type: it is not an expression at all, but a
         * built-in identifier the call reads by name — the rounding mode of {@code divide}
         * (spec 18.3), which {@code requireRoundingMode} has already checked is one. The emitter
         * reads its name and never asks for its type. */
        void untyped(int i) {
            Ast.Var name = (Ast.Var) args.get(i);
            cores[i] = new Core.Builtin(name.name(), name.pos());
        }

        /** The elaborated arguments. Every argument must have been reached: a rule that yields a type
         * without touching one of its arguments would leave the emitter a node with no type. */
        List<Core> cores() {
            List<Core> out = new ArrayList<>();
            for (int i = 0; i < cores.length; i++) {
                if (cores[i] == null) {
                    throw new IllegalStateException(
                            "argument " + (i + 1) + " was never typed at " + args.get(i).pos());
                }
                out.add(cores[i]);
            }
            return out;
        }
    }

    /**
     * The answer for a call this module has no callee for. Resolution already said what the name is,
     * and by here every answer it can give is something: a name it could not place is thrown out at
     * the top of {@link #typeOfCall}, where the report belongs to the position it was written at.
     * Telling the author of a name the compiler classified that it "is not a behavior or a builtin"
     * is discarding what the compiler knows and sending them after a typo they did not make — what is
     * wrong is the position, not the name.
     *
     * <p>Exhaustive over {@link ValueName} on purpose, with no default: a classification added later
     * cannot quietly fall through to a sentence that would be false about it. The three that reach an
     * author are the three a program can be written into. The rest name a call that should have been
     * expanded, substituted or rewritten before the check ran, which is this compiler disagreeing
     * with itself and not something an author can act on.
     */
    static RuntimeException noCallee(Ast.Apply call) {
        return switch (call.denotes()) {
            // a behavior named from a helper `let` or a `>->` composition, neither of which reaches
            // one (spec [#calling-a-behavior])
            case ValueName.Behavior _ -> CompileException.of(
                    Diagnostic.of("E1401", "e1401.behavior")
                            .title("e1401.title").at(call.pos(), call.written().length())
                            .args(call.written()).hint("e1401.behavior.hint", call.written())
                            .build(),
                    "`" + call.written() + "` is a behavior, and it cannot be called from here: a helper"
                            + " `let` does not reach one, and a `>->` composition is composed with"
                            + " rather than called (spec [#calling-a-behavior])");
            // A type applied to an argument is a construction, and every place a construction is
            // allowed rewrites it before the check reads it. Reaching here means it was written
            // somewhere no rewrite covers, so say what it is rather than what it is not.
            case ValueName.OfType named -> CompileException.of(
                    Diagnostic.of(null, "check.construct.position")
                            .title("check.construct.position.title")
                            .at(call.pos(), call.written().length()).args(named.name()).build(),
                    "`" + named.name() + "` is a type, so `" + named.name()
                            + "(...)` constructs one, and a construction cannot be written here");
            // A binding applied to arguments, whose type here is not a function. Either it is not one
            // — a value applied as though it were — or it has no type yet, which is what an inference
            // probe sees when it types a body before the binding it asks about has one and reads the
            // report to find out. The same sentence answers both: at the point of the report, this
            // name is not a function here.
            case ValueName.Local _ -> CompileException.of(
                    Diagnostic.of(null, "check.apply.notfunction")
                            .title("check.apply.notfunction.title")
                            .at(call.pos(), call.written().length()).args(call.written()).build(),
                    "`" + call.written() + "` is not a function here, so it cannot be applied to"
                            + " arguments");
            case ValueName.Helper _ -> unelaborated("a helper", call);
            case ValueName.Stdlib _ -> unelaborated("a standard-library function", call);
            // A name the language itself gives, applied. `Some`/`None` are told apart earlier (E1303),
            // so this is a rounding mode: a bare identifier the operation taking it reads, and not a
            // function. Reachable from the moment one ladder answers a name wherever it is written.
            case ValueName.Builtin b -> CompileException.of(
                    Diagnostic.of(null, "check.builtin.notfunction")
                            .title("check.apply.notfunction.title")
                            .at(call.pos(), call.written().length()).args(b.name()).build(),
                    "`" + b.name() + "` is a name the language gives, not a function, so it cannot"
                            + " be applied to arguments");
            // thrown out at the top of typeOfCall, before any of the work above
            case ValueName.Unresolved _ -> unelaborated("an unresolved name", call);
            case null -> unelaborated("nothing", call);
        };
    }

    private static IllegalStateException unelaborated(String what, Ast.Apply call) {
        return new IllegalStateException("`" + call.written() + "` denotes " + what
                + " and reached call elaboration unexpanded, at " + call.pos());
    }

    /**
     * The type of a call, by what the name it applies denotes.
     *
     * <p>Which of these a name is was answered when the module's names were resolved, so the order
     * the cases are written in here decides nothing. Before that this was a sequence of attempts —
     * the library, then a function-typed binding, then an injected behavior — and a name that could
     * be read two ways was whichever came first.
     */
    static Type typeOfCall(CallArgs ca, Ast.Apply call, Scope env, CheckContext ctx, Type expected) {
        List<Ast.Expr> args = call.args();
        if (call.denotes() == null) {
            throw new IllegalStateException(
                    "`" + call.written() + "` reached the check unresolved, at " + call.pos());
        }
        if (call.denotes() instanceof ValueName.Unresolved) {
            // reported where the name was written; this definition has no meaning to work out
            throw new Unanswerable(call.pos());
        }
        boolean library = call.denotes() instanceof ValueName.Stdlib;
        // A shipped intrinsic behaves like a built-in: check the call against its declared signature
        // (from the prelude) and yield its result type; the backend emits the primitive for its key.
        Prelude.IntrinsicSig intrinsic = library ? Prelude.intrinsics().get(call.reaches()) : null;
        // A declaration written with no parameter list is a value ([#fn-declaration]), and an empty
        // `()` would be a second spelling of it. The library was the last place that spelling was
        // still accepted.
        if (intrinsic != null && intrinsic.params().isEmpty()) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.apply.notfunction")
                            .title("check.apply.notfunction.title")
                            .at(call.pos(), call.written().length()).args(call.written())
                            .hint("check.stdlib.value.hint", call.written()).build(),
                    "`" + call.written() + "` is a value, not a function, so it takes no `()` — write `"
                            + call.written() + "` on its own");
        }
        if (intrinsic != null) {
            if (args.size() != intrinsic.params().size()) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.arity").title("check.arity.title")
                                .at(call.pos(), call.written().length())
                                .args(call.written(), intrinsic.params().size(), args.size()).build(),
                        call.written() + " takes " + intrinsic.params().size()
                                + " argument(s) but is called with " + args.size());
            }
            // The same three steps a helper's signature takes, for the same reasons: the context
            // pins what it can before anything is read, the value arguments fix the rest, and a
            // function argument is typed last — against parameter types the others have settled, so
            // a block written there has them to be checked at.
            //
            // The pin is for the step's sake. With no function argument there is nothing waiting on
            // it, and pinning anyway would answer an argument mismatch against the type the context
            // wanted rather than against the one the declaration asks for.
            boolean takesAFunction = intrinsic.params().stream().anyMatch(Type.FnOf.class::isInstance);
            Map<String, Type> bindings = new HashMap<>();
            if (takesAFunction) {
                BottomInfer.pinResultTypeVars(intrinsic.result(), expected, bindings, ctx.symbols(),
                        call.pos(), "result of " + call.written());
            }
            for (int i = 0; i < args.size(); i++) {
                if (intrinsic.params().get(i) instanceof Type.FnOf) {
                    continue;
                }
                // A rounding mode is not an expression: it is a name the operation taking it reads,
                // so it is checked as one and carries no type of its own ([#stdlib-decimal]).
                if (isRoundingMode(intrinsic.params().get(i))) {
                    requireRoundingMode(call.written(), args.get(i));
                    ca.untyped(i);
                    continue;
                }
                TypeOps.unify(intrinsic.params().get(i), ca.type(i), bindings, ctx.symbols(),
                        call.pos(), "argument " + (i + 1) + " of " + call.written());
            }
            for (int i = 0; i < args.size(); i++) {
                if (intrinsic.params().get(i) instanceof Type.FnOf declaredStep) {
                    ca.put(i, Elaborator.resolveStepBinding(call.written(), declaredStep, args.get(i),
                            bindings, env, ctx));
                    requiresOrderedKey(intrinsic.key(), call, declaredStep, bindings, ctx);
                }
            }
            Type result = TypeOps.substitute(intrinsic.result(), bindings);
            requiresOrdering(intrinsic.key(), call, result, ctx);
            if (intrinsic.key().equals("list.sum") || intrinsic.key().equals("list.product")) {
                return numericFold(call, result, expected);
            }
            if (intrinsic.key().equals("string.matches")) {
                validateRegexPattern(args.get(0));
            }
            return result;
        }
        return switch (library ? call.reaches() : "") {
            case "Date", "DateTime" -> {
                arity(call, 1);
                ca.type(0);   // the literal text, which temporalLiteral parses
                yield temporalLiteral(call);
            }
            default -> {
                // a function-typed value in scope (a helper's function parameter) applied to
                // arguments — f(x) (spec §fn-declaration). A newtype construction 金額(500) never
                // reaches here — NewtypeDesugar has lowered it to a NewData literal.
                // a function value in force, or a recursive helper's signature: which of the two
                // is the denotation's to say, and only one of them is bound here
                if (env.of(call.denotes(), call.written()) instanceof Type.FnOf fn) {
                    if (args.size() != fn.params().size()) {
                        throw CompileException.of(
                                Diagnostic.of(null, "check.arity").title("check.arity.title")
                                        .at(call.pos(), call.written().length())
                                        .args(call.written(), fn.params().size(), args.size()).build(),
                                "`" + call.written() + "` takes " + fn.params().size()
                                        + " argument(s) but is applied to " + args.size());
                    }
                    // Resolve the signature's type variables from the value (non-function) arguments
                    // first — a generic recursive helper like `foldFrom(step, seed, xs, i)` fixes `'acc`
                    // from the seed and `'a` from the list. An empty-collection seed ([], Map.empty)
                    // binds the accumulator to a bottom; the step's result then grows it to the concrete
                    // type, so a function argument's result refines the binding (as the old fold did).
                    Map<String, Type> bind = new HashMap<>();
                    // Pin the result-type variables from the surrounding context first (issue #70): a
                    // fold whose seed is Map.empty/[] has its accumulator `'acc` bound to the expected
                    // result BEFORE the step (and any inlined Map.upsert closure) is checked, so the
                    // seed's bottom no longer drives the step's parameter types.
                    BottomInfer.pinResultTypeVars(fn.result(), expected, bind, ctx.symbols(), call.pos(),
                            "result of " + call.written());
                    for (int i = 0; i < args.size(); i++) {
                        if (!(fn.params().get(i) instanceof Type.FnOf)) {
                            Type at = ca.type(i);
                            TypeOps.unify(fn.params().get(i), at, bind, ctx.symbols(), call.pos(), "argument " + (i + 1));
                        }
                    }
                    // Type the step (function) arguments. A fold over an empty-collection seed whose
                    // step needs the accumulator's element/value type can only get it from context;
                    // with no expected type the accumulator stays a bottom and the step fails deep in
                    // its (possibly inlined) body. Point at the seed — the empty collection whose type
                    // could not be inferred — rather than the arithmetic/match the bottom reached (#70).
                    try {
                        for (int i = 0; i < args.size(); i++) {
                            if (fn.params().get(i) instanceof Type.FnOf fp0) {
                                ca.put(i, Elaborator.resolveStepBinding(call.written(), fp0, args.get(i), bind, env, ctx));
                            }
                        }
                    } catch (CompileException stepError) {
                        // Only re-point at the seed when the failure is genuinely the unresolved bottom:
                        // an empty-collection seed whose accumulator type nothing fixed, and an error
                        // that actually reported that bottom (`_`). An unrelated error in the step (an
                        // unknown identifier, a real type clash) is rethrown untouched so it is not
                        // masked. This fires whether or not a context type was pushed — an expected type
                        // that did not fit still leaves the accumulator a bottom (issue #70).
                        int seed = BottomInfer.untypedEmptySeed(args, fn, bind, call.pos());
                        if (seed < 0 || !BottomInfer.reportsUnresolvedBottom(stepError)) {
                            throw stepError;
                        }
                        Diagnostic.Builder b = Diagnostic.of(null, "check.fold.seed.untyped")
                                .title("check.fold.seed.title")
                                .at(args.get(seed).pos(), Elaborator.width(args.get(seed)));
                        if (stepError.diagnostic() != null && stepError.diagnostic().region() != null) {
                            b.secondary(stepError.diagnostic().region(), "check.fold.seed.here");
                        }
                        throw CompileException.of(b.build(),
                                "cannot infer the element type of the empty collection seeding `"
                                        + call.written() + "`; annotate the declaration it feeds");
                    }
                    for (int i = 0; i < args.size(); i++) {
                        if (!(fn.params().get(i) instanceof Type.FnOf)) {
                            ca.require(i, TypeOps.substitute(fn.params().get(i), bind), "argument " + (i + 1) + " of " + call.written());
                        }
                    }
                    yield TypeOps.substitute(fn.result(), bind);
                }
                // a library qualifier that matched no builtin or intrinsic above is a wrong stdlib
                // call (spec §stdlib) — report it as such, not as a missing behavior.
                if (library || call.written().indexOf('.') >= 0) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.stdlib.notfunction").title("check.unknown.title")
                                    .at(call.pos(), call.written().length()).args(call.written()).build(),
                            "`" + call.written() + "` is not a standard-library function.");
                }
                // a required behavior called inline (spec 12.2, 13), or one that requires nothing and
                // is called by name (spec [#calling-a-behavior]). Both are typed against the callee's
                // declaration; where the behavior comes from at run time is the backend's to know.
                ReqSig callee = ctx.reqs().get(call.reaches());
                if (callee == null) {
                    callee = ctx.callees().get(call.reaches());
                }
                if (callee == null) {
                    Elaborator.optionCaseWritten(call.written(), call.pos());
                    String qualified = Prelude.qualifiedFor(call.written());
                    if (qualified != null) {
                        throw CompileException.of(
                                Diagnostic.of(null, "check.stdlib.qualified.msg")
                                        .title("check.unknown.title").at(call.pos(), call.written().length())
                                        .args(call.written(), qualified).build(),
                                "`" + call.written() + "` is a standard-library function and must be called"
                                        + " qualified, as `" + qualified + "` (spec §stdlib).");
                    }
                    throw noCallee(call);
                }
                arity(call, callee.params().size());
                for (int i = 0; i < callee.params().size(); i++) {
                    ca.require(i, callee.params().get(i), "argument " + (i + 1) + " of " + call.written());
                }
                yield callee.success();
            }
        };
    }

    /**
     * The constant a newtype construction wraps, if its {@code value} argument folds — for
     * {@code 金額(500)} (lowered to {@code 金額 { value = 500 }} by NewtypeDesugar) or the record
     * form written directly. Empty when the argument is a runtime value or the data is not a
     * single-{@code value} wrapper (e.g. a product).
     */
    static Optional<Object> newtypeConstantArg(Ast.NewData nd) {
        if (nd.spreads().isEmpty() && nd.inits().size() == 1
                && nd.inits().get(0).name().equals("value")) {
            return ConstEval.eval(nd.inits().get(0).value());
        }
        return Optional.empty();
    }

    /** A rounding mode is one of the built-in identifiers, written bare — not an ordinary
     * expression ([#stdlib-decimal]). {@code of} is the operation taking it. */
    static void requireRoundingMode(String of, Ast.Expr e) {
        if (!(e instanceof Ast.Var v) || !Elaborator.ROUNDING_MODES.contains(v.name())) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.divide.rounding").title("check.type.mismatch.title")
                            .at(e.pos()).args(of).build(),
                    "the rounding mode of `" + of + "` must be one of HALF_UP, HALF_EVEN, HALF_DOWN,"
                            + " UP, DOWN, CEILING, FLOOR ([#stdlib-decimal])");
        }
    }

    /** The pattern of {@code String.matches} must evaluate to a string at compile time, so it is
     * validated (and can be compiled) there: a malformed regex is a compile error, not a runtime
     * exception, and the value it constrains is proven at construction (spec §stdlib-string). A
     * literal is one such expression and so is a {@code ++} of literals and of a module's values,
     * which is what lets several formats share a part (issue #208). What is validated is the string
     * the whole expression composes to, not the pieces it was written in. */
    static void validateRegexPattern(Ast.Expr e) {
        String pattern = ConstEval.evalString(e).orElse(null);
        if (pattern == null) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.matches.constant").title("check.type.mismatch.title")
                            .at(e.pos()).build(),
                    "the pattern of `String.matches` must evaluate to a string at compile time — a"
                            + " string literal, or literals and values named by a top-level `let`"
                            + " joined with `++`");
        }
        try {
            java.util.regex.Pattern.compile(pattern);
        } catch (java.util.regex.PatternSyntaxException ex) {
            // getDescription() is the one-line reason ("Unclosed character class near index 3");
            // getMessage() would also dump the pattern and a caret, which the source region already shows.
            throw CompileException.of(
                    Diagnostic.of(null, "check.matches.regex").title("check.type.mismatch.title")
                            .at(e.pos()).args(ex.getDescription()).build(),
                    "`String.matches` pattern is not a valid regular expression: " + ex.getDescription());
        }
    }

    /** A stdlib argument-type error: {@code subject} (a function name) expects a container of kind
     * {@code kindKey} (a localized phrase such as "a List"), but got {@code actual}. */
    static CompileException expects(SourcePos pos, String subject, String kindKey, Type actual,
                                            String legacy) {
        return CompileException.of(
                Diagnostic.of(null, "check.expects").title("check.type.mismatch.title").at(pos)
                        .args(subject, Localizable.of(kindKey), Type.show(actual)).build(),
                legacy);
    }

    /**
     * The element {@code List.sum} / {@code List.product} answers with. It is {@code Int} or
     * {@code Decimal} — the two types {@code +} and {@code *} are defined for — and nothing else:
     * a newtype over one of them declares neither an addition nor a zero, so it is rejected here
     * rather than folded as the value it wraps.
     *
     * <p>Over the empty-list literal there is no element to read, and the seed the fold answers with
     * is {@code 0} or {@code 0.0m} by which of the two this is. That comes from the position the call
     * is written in — the field, the annotated binding, the declared output it feeds. A {@code ?}
     * field asks for the value it wraps rather than for an optional (ADR-0011), so the optional is
     * peeled before the position is read, exactly as a written literal has it peeled.
     *
     * <p>Three things the position can be, and they are three different reports. It states one of
     * the two: that is the answer. It states nothing: the answer is asked for rather than defaulted,
     * since defaulting to {@code Int} would make a numeric-literal default rule out of one library
     * function. It states something else: nothing about the element is unknown, and what is wrong is
     * that a sum does not go here — asking for an annotation would send the reader after something
     * the position already carries.
     */
    private static Type numericFold(Ast.Apply call, Type element, Type expected) {
        if (element == Type.INT || element == Type.DECIMAL) {
            return element;
        }
        if (BottomInfer.isBottom(element)) {
            Type position = expected instanceof Type.OptionOf o ? o.element() : expected;
            if (position == Type.INT || position == Type.DECIMAL) {
                return position;
            }
            if (position == null || BottomInfer.isBottom(position)) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.numeric.empty").title("check.fold.seed.title")
                                .at(call.pos(), call.written().length()).args(call.written())
                                .hint("check.numeric.empty.hint").build(),
                        call.written() + " over the empty list answers with its seed, and whether that"
                                + " seed is an Int or a Decimal follows from an element the empty"
                                + " list does not have — annotate the position it feeds"
                                + " (`let total: Decimal = " + call.written() + "([])`)");
            }
            throw CompileException.of(
                    Diagnostic.of(null, "check.numeric.result").title("check.type.mismatch.title")
                            .at(call.pos(), call.written().length())
                            .args(call.written(), Type.show(position))
                            .hint("check.numeric.result.hint").build(),
                    call.written() + " answers with an Int or a Decimal, but this position needs "
                            + Type.show(position) + " — a newtype over one of them is built from the"
                            + " result (`Hours(" + call.written() + "(xs))`) rather than being it, and any"
                            + " other type has no place for one");
        }
        throw CompileException.of(
                Diagnostic.of(null, "check.numeric").title("check.type.mismatch.title")
                        .at(call.pos(), call.written().length())
                        .args(call.written(), Localizable.of("kind.numeric.list"), Type.show(element))
                        .hint("check.numeric.hint").build(),
                shortName(call.written()) + " needs a list of Int or Decimal, but the element is "
                        + Type.show(element) + " — map to its numeric field first and apply "
                        + call.written() + " to that");
    }

    /** The name without its qualifier: {@code List.sum} reads as {@code sum} in a sentence about the
     * function itself, and a call may be written either way. */
    private static String shortName(String fn) {
        int dot = fn.indexOf('.');
        return dot < 0 ? fn : fn.substring(dot + 1);
    }

    /** A stdlib error where a list's element (or a key) must be an ordered primitive to sort/compare. */
    static CompileException needsOrdered(SourcePos pos, String subject, Type element, String legacy) {
        return CompileException.of(
                Diagnostic.of(null, "check.ordered").title("check.type.mismatch.title").at(pos)
                        .args(subject, Localizable.of("kind.ordered.list"), Type.show(element))
                        .hint("check.ordered.hint").build(),
                legacy);
    }

    /** A written date — {@code Date("2026-07-01")} / {@code DateTime("2026-07-01T09:00")}. The
     * argument must be a string literal: the compiler parses it here, so a malformed date fails the
     * build rather than a run (and an {@code example} fixture, which may only hold literals, can
     * carry a date at all). A computed date comes from the boundary or from {@code Date.addDays},
     * not from this form. */
    static Type temporalLiteral(Ast.Apply call) {
        boolean isDate = "Date".equals(call.reaches());
        if (!(call.args().get(0) instanceof Ast.StringLit lit)) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.temporal.literal").title("check.type.mismatch.title")
                            .at(call.pos(), call.written().length()).args(call.written()).build(),
                    "`" + call.written() + "(...)` takes a written string, e.g. "
                            + (isDate ? "Date(\"2026-07-01\")" : "DateTime(\"2026-07-01T09:00\")"));
        }
        parseTemporal(call.written(), lit.value(), call.pos());
        return isDate ? Type.DATE : Type.DATETIME;
    }

    /** Parses a written temporal, reporting a malformed one against {@code pos}. Returns the parsed
     * value so the backend and the example verifier share this one reading of the text. */
    public static Object parseTemporal(String fn, String text, SourcePos pos) {
        try {
            return fn.equals("Date")
                    ? java.time.LocalDate.parse(text)
                    : java.time.LocalDateTime.parse(text);
        } catch (java.time.format.DateTimeParseException _) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.temporal.malformed").title("check.type.mismatch.title")
                            .at(pos, fn.length()).args(fn, text).build(),
                    "`" + text + "` is not a " + fn + " (expected "
                            + (fn.equals("Date") ? "YYYY-MM-DD" : "YYYY-MM-DDTHH:mm[:ss]") + ")");
        }
    }

    static void arity(Ast.Apply call, int n) {
        if (call.args().size() != n) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.arity").title("check.arity.title")
                            .at(call.pos(), call.written().length())
                            .args(call.written(), n, call.args().size()).build(),
                    call.written() + " expects " + n + " argument(s), got " + call.args().size());
        }
    }
}
