package souther.compiler.check;

import souther.compiler.Prelude;
import souther.compiler.ast.Ast;
import souther.compiler.core.Core;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import java.util.Set;
import souther.compiler.diag.Localizable;
import souther.compiler.diag.SourcePos;

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
    private static Set<TypeName> primitiveHeaded(Type head, String errorCase) {
        return new java.util.LinkedHashSet<>(
                List.of(TypeName.primitive(Type.show(head)), TypeName.runtime(errorCase)));
    }

    static Core elaborateCall(Ast.Call call, Map<String, Type> env, CheckContext ctx,
                                      Type expected) {
        CallArgs ca = new CallArgs(call.args(), env, ctx);
        Type result = typeOfCall(ca, call, env, ctx, expected);
        return new Core.Call(call.fn(), ca.cores(), result, call.pos());
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
        private final Map<String, Type> env;
        private final CheckContext ctx;

        CallArgs(List<Ast.Expr> args, Map<String, Type> env, CheckContext ctx) {
            this.args = args;
            this.cores = new Core[args.size()];
            this.env = env;
            this.ctx = ctx;
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
            cores[i] = new Core.Var(name.name(), null, name.pos());
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

    static Type typeOfCall(CallArgs ca, Ast.Call call, Map<String, Type> env, CheckContext ctx, Type expected) {
        List<Ast.Expr> args = call.args();
        // A shipped intrinsic behaves like a built-in: check the call against its declared signature
        // (from the prelude) and yield its result type; the backend emits the primitive for its key.
        Prelude.IntrinsicSig intrinsic = Prelude.intrinsics().get(call.fn());
        if (intrinsic != null) {
            if (args.size() != intrinsic.params().size()) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.arity").title("check.arity.title")
                                .at(call.pos(), call.fn().length())
                                .args(call.fn(), intrinsic.params().size(), args.size()).build(),
                        call.fn() + " takes " + intrinsic.params().size()
                                + " argument(s) but is called with " + args.size());
            }
            Map<String, Type> bindings = new HashMap<>();
            for (int i = 0; i < args.size(); i++) {
                Type argType = ca.type(i);
                TypeOps.unify(intrinsic.params().get(i), argType, bindings, ctx.symbols(), call.pos(),
                        "argument " + (i + 1) + " of " + call.fn());
            }
            Type result = TypeOps.substitute(intrinsic.result(), bindings);
            // `sort` carries no `comparable` constraint in its `List<'a>` signature (Souther has no
            // type classes), so guard here: an ordered value sorts — an ordered primitive, or a
            // newtype over one, which carries its ordering as Comparable. A product data does not,
            // and would throw at runtime, so reject it now. The empty-list literal (element
            // `Nothing`) is fine: it sorts to itself, so let it through.
            if (intrinsic.key().equals("list.sort") && result instanceof Type.ListOf lo
                    && !(lo.element() instanceof Type.Nothing)
                    && !TypeOps.isOrderedValue(lo.element(), ctx.symbols())) {
                throw needsOrdered(call.pos(), "sort", lo.element(),
                        "sort needs a list of ordered values (Int, String, Decimal, Date, DateTime, or"
                                + " a newtype over one of these), but the element is " + lo.element()
                                + " — sort its ordered field instead (e.g. map to it first)");
            }
            if (intrinsic.key().equals("string.matches")) {
                validateRegexPattern(args.get(0));
            }
            return result;
        }
        return switch (call.fn()) {
            case "String.length" -> {
                arity(call, 1);
                ca.require(0, Type.STRING, "argument of String.length");
                yield Type.INT;
            }
            case "String.toInt" -> {
                arity(call, 1);
                ca.require(0, Type.STRING, "argument of String.toInt");
                // a non-numeric string produces the NotANumber case; a primitive-headed union a core
                // declaration cannot name, so this stays a built-in like Int.divide
                yield Type.union(primitiveHeaded(Type.INT, "NotANumber"));
            }
            case "String.toDecimal" -> {
                arity(call, 1);
                ca.require(0, Type.STRING, "argument of String.toDecimal");
                // the sibling of toInt, and here for the same reason: a primitive-headed union
                yield Type.union(primitiveHeaded(Type.DECIMAL, "NotANumber"));
            }
            case "List.length" -> {
                arity(call, 1);
                Type t = ca.type(0);
                if (!(t instanceof Type.ListOf)) {
                    throw expects(call.pos(), "List.length", "kind.list", t,
                            "argument of List.length must be a List but is " + t);
                }
                yield Type.INT;
            }
            case "List.max", "List.min" -> {
                arity(call, 1);
                Type t = ca.type(0);
                if (!(t instanceof Type.ListOf lo)) {
                    throw expects(call.pos(), call.fn(), "kind.list", t,
                            "argument of " + call.fn() + " must be a List but is " + t);
                }
                // Like `sort`, max/min compare by natural order, so the element must be an ordered
                // value (Souther has no type classes); a product data is not Comparable. The
                // empty-list literal (element `Nothing`) is fine — its result is `None`.
                if (!BottomInfer.isBottom(lo.element())
                        && !TypeOps.isOrderedValue(lo.element(), ctx.symbols())) {
                    throw needsOrdered(call.pos(), call.fn(), lo.element(),
                            call.fn() + " needs a list of ordered values (Int, String, Decimal, Date,"
                                    + " DateTime, or a newtype over one of these), but the element is "
                                    + lo.element() + " — compare its ordered field instead");
                }
                yield Type.option(lo.element());
            }
            case "List.find" -> {
                arity(call, 2);   // find(p, xs): predicate first, list last (F#/Elm order)
                Type t = ca.type(1);
                if (!(t instanceof Type.ListOf lo)) {
                    throw expects(call.pos(), "List.find", "kind.list", t,
                            "List.find expects a List, got " + t);
                }
                Type pr = ca.block(0, call.fn(), List.of(lo.element()));
                if (pr != Type.BOOL) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.fn.predicatebool").title("check.fn.title")
                                    .at(call.pos()).args("List.find", Type.show(pr)).build(),
                            "List.find's predicate must return Bool, but returns " + pr);
                }
                yield Type.option(lo.element());
            }
            case "Option.map" -> {
                arity(call, 2);   // map(f, opt): function first, option last (F#/Elm order)
                Type t = ca.type(1);
                if (!(t instanceof Type.OptionOf oo)) {
                    throw expects(call.pos(), "Option.map", "kind.option", t,
                            "Option.map expects an Option, got " + t);
                }
                // `f` sees the contained value; the option's element type gives its one parameter type.
                // The result re-wraps `f`'s return, so the whole call is `Option<'b>`.
                Type r = ca.block(0, call.fn(), List.of(oo.element()));
                yield Type.option(r);
            }
            case "List.sortBy" -> {
                arity(call, 2);   // sortBy(key, xs): key first, list last (F#/Elm order)
                Type t = ca.type(1);
                if (!(t instanceof Type.ListOf lo)) {
                    throw expects(call.pos(), "List.sortBy", "kind.list", t,
                            "List.sortBy expects a List, got " + t);
                }
                Type keyT = ca.block(0, call.fn(), List.of(lo.element()));
                if (!BottomInfer.isBottom(keyT) && !TypeOps.isOrderedValue(keyT, ctx.symbols())) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.ordered.key").title("check.type.mismatch.title")
                                    .at(call.pos()).args("List.sortBy", Type.show(keyT))
                                    .hint("check.ordered.hint").build(),
                            "List.sortBy's key must be an ordered value (Int, String, Decimal, Date,"
                                    + " DateTime, or a newtype over one of these), but returns " + keyT);
                }
                yield Type.list(lo.element());
            }
            case "List.get" -> {
                arity(call, 2);
                Type first = ca.type(1);   // get(index, xs): list last
                if (!(first instanceof Type.ListOf lo)) {
                    throw expects(call.pos(), "List.get", "kind.list", first,
                            "List.get expects a List, got " + first);
                }
                ca.require(0, Type.INT, "index of List.get");
                yield Type.option(lo.element());
            }
            case "Map.get" -> {
                arity(call, 2);
                Type first = ca.type(1);   // get(key, m): map last
                if (!(first instanceof Type.MapOf mo)) {
                    throw expects(call.pos(), "Map.get", "kind.map", first,
                            "Map.get expects a Map, got " + first);
                }
                // A bottom key type is a `Map.empty`-seeded accumulator whose key is not fixed yet;
                // the block growing it — `Map.get(k, acc)` in a groupBy fold — supplies the real key,
                // so accept it rather than demand the bottom. Otherwise the key must match.
                if (!BottomInfer.isBottom(mo.key())) {
                    ca.require(0, mo.key(), "key of Map.get");
                } else {
                    ca.type(0);   // nothing to check it against yet, but the key is still typed
                }
                yield Type.option(mo.value());
            }
            case "Map.empty" -> {
                arity(call, 0);
                // like `[]`, the empty map's key and value are bottoms fixed by context (ADR-0028).
                // When the context supplies an expected map type, adopt it directly so the value type
                // is concrete from the start — a Map.empty()-seeded fold no longer forces its
                // accumulator (and any updater closure) to a bottom.
                yield expected instanceof Type.MapOf me ? me : Type.map(Type.NOTHING, Type.NOTHING);
            }
            case "Set.empty" -> {
                arity(call, 0);
                // empty set's element type fixed by context (ADR-0028); adopt an expected set type
                yield expected instanceof Type.SetOf se ? se : Type.set(Type.NOTHING);
            }
            case "Date", "DateTime" -> {
                arity(call, 1);
                ca.type(0);   // the literal text, which temporalLiteral parses
                yield temporalLiteral(call);
            }
            case "Int.remainder" -> {
                arity(call, 2);
                ca.require(0, Type.INT, "argument 1 of remainder");
                ca.require(1, Type.INT, "argument 2 of remainder");
                // partial: a zero divisor produces the DivisionByZero case (spec 18.2)
                yield Type.union(primitiveHeaded(Type.INT, "DivisionByZero"));
            }
            case "Decimal.toInt" -> {
                // The narrowing states its rounding, as `divide` does: dropping a fraction is a
                // domain decision (spec 18.3). The widening `Decimal.fromInt` needs no such word and
                // is an ordinary stdlib function.
                arity(call, 2);
                ca.require(0, Type.DECIMAL, "argument 1 of toInt");
                requireRoundingMode(args.get(1));
                ca.untyped(1);   // a built-in identifier, not an expression
                yield Type.INT;
            }
            case "Decimal.round" -> {
                // Rounding to a scale names its mode for the same reason `toInt` does, and stays in
                // the compiler for the same reason: the mode is a bare built-in identifier, which a
                // core declaration's parameter type cannot name (spec 18.3).
                arity(call, 3);
                ca.require(0, Type.DECIMAL, "argument 1 of round");
                ca.require(1, Type.INT, "scale of round");
                requireRoundingMode(args.get(2));
                ca.untyped(2);   // a built-in identifier, not an expression
                yield Type.DECIMAL;
            }
            case "Int.divide", "Decimal.divide" -> {
                if (args.size() == 4) {
                    // Decimal divide states its rounding: divide(a, b, scale, mode) (spec 18.3)
                    ca.require(0, Type.DECIMAL, "argument 1 of divide");
                    ca.require(1, Type.DECIMAL, "argument 2 of divide");
                    ca.require(2, Type.INT, "scale of divide");
                    requireRoundingMode(args.get(3));
                    ca.untyped(3);   // a built-in identifier, not an expression
                    yield Type.union(primitiveHeaded(Type.DECIMAL, "DivisionByZero"));
                }
                arity(call, 2);
                ca.require(0, Type.INT, "argument 1 of divide");
                ca.require(1, Type.INT, "argument 2 of divide");
                yield Type.union(primitiveHeaded(Type.INT, "DivisionByZero"));
            }
            default -> {
                // a function-typed value in scope (a helper's function parameter) applied to
                // arguments — f(x) (spec §fn-declaration). A newtype construction 金額(500) never
                // reaches here — NewtypeDesugar has lowered it to a NewData literal.
                if (env.get(call.fn()) instanceof Type.FnOf fn) {
                    if (args.size() != fn.params().size()) {
                        throw CompileException.of(
                                Diagnostic.of(null, "check.arity").title("check.arity.title")
                                        .at(call.pos(), call.fn().length())
                                        .args(call.fn(), fn.params().size(), args.size()).build(),
                                "`" + call.fn() + "` takes " + fn.params().size()
                                        + " argument(s) but is applied to " + args.size());
                    }
                    // Resolve the signature's type variables from the value (non-function) arguments
                    // first — a generic recursive helper like `foldFrom(step, seed, xs, i)` fixes `'acc`
                    // from the seed and `'a` from the list. An empty-collection seed ([], Map.empty)
                    // binds the accumulator to a bottom; the step's result then grows it to the concrete
                    // type, so a function argument's result refines the binding (as the old fold did).
                    Map<String, Type> bind = new HashMap<>();
                    // Pin the result-type variables from the surrounding context first (issue #70): a
                    // fold whose seed is Map.empty()/[] has its accumulator `'acc` bound to the expected
                    // result BEFORE the step (and any inlined Map.upsert closure) is checked, so the
                    // seed's bottom no longer drives the step's parameter types.
                    BottomInfer.pinResultTypeVars(fn.result(), expected, bind, ctx.symbols(), call.pos(),
                            "result of " + call.fn());
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
                                ca.put(i, Elaborator.resolveStepBinding(call.fn(), fp0, args.get(i), bind, env, ctx));
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
                                        + call.fn() + "`; annotate the declaration it feeds");
                    }
                    for (int i = 0; i < args.size(); i++) {
                        if (!(fn.params().get(i) instanceof Type.FnOf)) {
                            ca.require(i, TypeOps.substitute(fn.params().get(i), bind), "argument " + (i + 1) + " of " + call.fn());
                        }
                    }
                    yield TypeOps.substitute(fn.result(), bind);
                }
                // a qualified name that matched no stdlib builtin/intrinsic above is a wrong stdlib
                // call (spec §stdlib) — report it as such, not as a missing behavior.
                if (call.fn().indexOf('.') >= 0) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.stdlib.notfunction").title("check.unknown.title")
                                    .at(call.pos(), call.fn().length()).args(call.fn()).build(),
                            "`" + call.fn() + "` is not a standard-library function.");
                }
                // a required behavior called inline (spec 12.2, 13): type it as its success case
                ReqSig callee = ctx.reqs().get(call.fn());
                if (callee == null) {
                    String qualified = Prelude.qualifiedFor(call.fn());
                    if (qualified != null) {
                        throw CompileException.of(
                                Diagnostic.of(null, "check.stdlib.qualified.msg")
                                        .title("check.unknown.title").at(call.pos(), call.fn().length())
                                        .args(call.fn(), qualified).build(),
                                "`" + call.fn() + "` is a standard-library function and must be called"
                                        + " qualified, as `" + qualified + "` (spec §stdlib).");
                    }
                    throw CompileException.of(
                            Diagnostic.of("E1401", "e1401.msg").at(call.pos(), call.fn().length())
                                    .args(call.fn())
                                    .suggestion(Suggest.candidate(call.fn(), ctx.reqs().keySet()))
                                    .hint("e1401.hint")
                                    .build(),
                            "`" + call.fn() + "` is not a behavior or builtin"
                                    + Suggest.hint(call.fn(), ctx.reqs().keySet())
                                    + ". Calling arbitrary JVM methods is not allowed; declare a behavior"
                                    + " without a `let` and implement it from Java.");
                }
                arity(call, callee.params().size());
                for (int i = 0; i < callee.params().size(); i++) {
                    ca.require(i, callee.params().get(i), "argument " + (i + 1) + " of " + call.fn());
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

    /** The rounding-mode argument of {@code divide} is one of the built-in identifiers, written
     * bare — not an ordinary expression (spec 18.3). */
    static void requireRoundingMode(Ast.Expr e) {
        if (!(e instanceof Ast.Var v) || !Elaborator.ROUNDING_MODES.contains(v.name())) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.divide.rounding").title("check.type.mismatch.title")
                            .at(e.pos()).build(),
                    "the rounding mode of `divide` must be one of HALF_UP, HALF_EVEN, HALF_DOWN, UP,"
                            + " DOWN, CEILING, FLOOR (spec 18.3)");
        }
    }

    /** The pattern of {@code String.matches} must be a string literal, so it is validated (and can be
     * compiled) at compile time: a malformed regex is a compile error, not a runtime exception, and
     * the value it constrains is proven at construction (spec §stdlib-string). */
    static void validateRegexPattern(Ast.Expr e) {
        if (!(e instanceof Ast.StringLit lit)) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.matches.literal").title("check.type.mismatch.title")
                            .at(e.pos()).build(),
                    "the pattern of `String.matches` must be a string literal, so it can be validated"
                            + " at compile time");
        }
        try {
            java.util.regex.Pattern.compile(lit.value());
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
    static Type temporalLiteral(Ast.Call call) {
        boolean isDate = call.fn().equals("Date");
        if (!(call.args().get(0) instanceof Ast.StringLit lit)) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.temporal.literal").title("check.type.mismatch.title")
                            .at(call.pos(), call.fn().length()).args(call.fn()).build(),
                    "`" + call.fn() + "(...)` takes a written string, e.g. "
                            + (isDate ? "Date(\"2026-07-01\")" : "DateTime(\"2026-07-01T09:00\")"));
        }
        parseTemporal(call.fn(), lit.value(), call.pos());
        return isDate ? Type.DATE : Type.DATETIME;
    }

    /** Parses a written temporal, reporting a malformed one against {@code pos}. Returns the parsed
     * value so the backend and the example verifier share this one reading of the text. */
    public static Object parseTemporal(String fn, String text, SourcePos pos) {
        try {
            return fn.equals("Date")
                    ? java.time.LocalDate.parse(text)
                    : java.time.LocalDateTime.parse(text);
        } catch (java.time.format.DateTimeParseException e) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.temporal.malformed").title("check.type.mismatch.title")
                            .at(pos, fn.length()).args(fn, text).build(),
                    "`" + text + "` is not a " + fn + " (expected "
                            + (fn.equals("Date") ? "YYYY-MM-DD" : "YYYY-MM-DDTHH:mm[:ss]") + ")");
        }
    }

    static void arity(Ast.Call call, int n) {
        if (call.args().size() != n) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.arity").title("check.arity.title")
                            .at(call.pos(), call.fn().length())
                            .args(call.fn(), n, call.args().size()).build(),
                    call.fn() + " expects " + n + " argument(s), got " + call.args().size());
        }
    }
}
