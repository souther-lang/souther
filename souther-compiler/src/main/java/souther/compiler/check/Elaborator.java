package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.core.Core;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Types an expression and produces the Core node for it, carrying the type this decided (issue #81):
 * the backend emits from what this returns instead of inferring the same types a second time.
 *
 * <p>The switch over expression kinds is here; the kinds with rules of their own live next door —
 * {@link CallElaborator}, {@link BinaryElaborator}, {@link MatchElaborator} — and the bottom an
 * empty collection carries is {@link BottomInfer}'s.
 */
public final class Elaborator {

    private Elaborator() {}

    // --- expression typing (shared with the backend) ---

    /** No required behaviors are in scope (decoders, encoders, invariants — spec 9.3, 17). */
    static final Map<String, ReqSig> NO_REQS = Map.of();


    public static Type typeOf(Ast.Expr e, Map<String, Type> env, CheckContext ctx) {
        return typeOf(e, env, ctx, null);
    }

    /** The type of {@code e}, discarding the Core the elaboration produced — for the checks that ask
     * only whether an expression types (a decoder, an invariant, a helper's standalone check). */
    public static Type typeOf(Ast.Expr e, Map<String, Type> env, CheckContext ctx, Type expected) {
        return elaborate(e, env, ctx, expected).type();
    }

    public static Core elaborate(Ast.Expr e, Map<String, Type> env, CheckContext ctx) {
        return elaborate(e, env, ctx, null);
    }

    /**
     * Types {@code e} and produces the Core node for it, carrying the type this decided (issue #81).
     * The backend emits from what this returns instead of inferring the same types a second time.
     *
     * <p>Bidirectional typing: {@code expected} is the type this expression is checked against, pushed
     * down from the surrounding context (a declared field type, a declared return type). It may be
     * {@code null} — no context — in which case this behaves exactly as pure bottom-up synthesis.
     * Only a few arms consume it: the empty-collection leaves ([], Map.empty, Set.empty) adopt it,
     * and a generic call pre-binds its result-type variables from it, so a fold whose seed is an
     * empty collection has its accumulator pinned by context before the step is checked.
     */
    public static Core elaborate(Ast.Expr e, Map<String, Type> env, CheckContext ctx, Type expected) {
        return equatableCollections(elaborating(e, env, ctx, expected));
    }

    /**
     * Refuses a {@code Set} or a {@code Map} that would have to compare a function. Asked of what
     * elaboration decided rather than of what was written, because such a collection need not be
     * written to exist: {@code List.distinct} grows a seen-set of its elements, and only the
     * elaborated type says what those are.
     */
    private static Core equatableCollections(Core c) {
        TypeOps.UncomparableIn bad = TypeOps.uncomparableCollection(c.type());
        if (bad == null) {
            return c;
        }
        // which collection asked is part of the answer: a Set asks whether two elements are equal and
        // a Map whether two keys are, and the report says which of the two it was
        String key = bad instanceof TypeOps.UncomparableIn.MapKey
                ? "check.map.key.function" : "check.set.function";
        String what = bad instanceof TypeOps.UncomparableIn.MapKey ? "key" : "element";
        throw CompileException.of(
                Diagnostic.of(null, key).title("check.boundary.title")
                        .at(c.pos()).args(Type.show(bad.type())).build(),
                "this collection would have to compare " + Type.show(bad.type()) + " as its " + what
                        + ", and a function has no value to compare");
    }

    private static Core elaborating(Ast.Expr e, Map<String, Type> env, CheckContext ctx,
                                    Type expected) {
        return switch (e) {
            case Ast.IntLit x -> new Core.Int(x.value(), Type.INT, x.pos());
            case Ast.DecimalLit x -> new Core.Decimal(x.value(), Type.DECIMAL, x.pos());
            case Ast.StringLit x -> new Core.Str(x.value(), Type.STRING, x.pos());
            case Ast.BoolLit x -> new Core.Bool(x.value(), Type.BOOL, x.pos());
            case Ast.Tuple tup -> {
                // A pushed-down tuple type reaches each element, so a written `(Set<Int>, List<Int>)`
                // fixes the empty collections the tuple seeds rather than leaving them bottoms (#74).
                List<Type> want = expected instanceof Type.TupleOf te
                        && te.elements().size() == tup.elements().size() ? te.elements() : null;
                List<Core> elems = new ArrayList<>();
                List<Type> elemTypes = new ArrayList<>();
                for (int i = 0; i < tup.elements().size(); i++) {
                    Core el = elaborate(tup.elements().get(i), env, ctx,
                            want == null ? null : want.get(i));
                    elems.add(el);
                    elemTypes.add(el.type());
                }
                yield new Core.Tuple(elems, Type.tuple(elemTypes), tup.pos());
            }
            case Ast.TupleGet tg -> {
                Core tuple = elaborate(tg.tuple(), env, ctx);
                Type tt = tuple.type();
                if (!(tt instanceof Type.TupleOf to)) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.tuple.pattern").title("check.type.mismatch.title")
                                    .at(tg.pos()).args(Type.show(tt)).build(),
                            "a tuple pattern needs a tuple, got " + tt);
                }
                if (to.elements().size() != tg.arity()) {   // exact arity, in either direction (Elm)
                    throw CompileException.of(
                            Diagnostic.of(null, "check.tuple.arity").title("check.type.mismatch.title")
                                    .at(tg.pos()).args(tg.arity(), to.elements().size()).build(),
                            "this pattern binds " + tg.arity()
                                    + " name(s) but the tuple has " + to.elements().size() + " element(s)");
                }
                yield new Core.TupleGet(tuple, tg.index(), tg.arity(),
                        to.elements().get(tg.index()), tg.pos());
            }
            case Ast.Neg neg -> {
                Core operand = elaborate(neg.operand(), env, ctx);
                Type t = operand.type();
                if (t != Type.INT && t != Type.DECIMAL) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.neg.msg")
                                    .title("check.neg.title")
                                    .at(neg.pos(), width(neg.operand()))
                                    .args(Type.show(t))
                                    .build(),
                            "unary minus needs an Int or Decimal, got " + t);
                }
                yield new Core.Neg(operand, t, neg.pos());
            }
            case Ast.LetIn li -> {
                Type annotation = annotatedType(li, ctx.symbols());
                Core value;
                Type bindType;
                if (annotation instanceof Type.FnOf declared && producesFunction(li.value())) {
                    // the written type says what the function takes, so nothing has to be read off
                    // the applications — which is what a function passed on rather than applied has
                    // none of, and what a function applied only inside a lambda cannot give
                    value = elaborateFunctionValue(li.value(), declared.params(), env, ctx);
                    checkLetAnnotation(li, declared, value.type(), ctx.symbols());
                    bindType = declared;
                } else if (isFunctionSelection(li.value())) {
                    // a lambda bound to a local that could not be inlined (e.g. chosen by an `if`):
                    // it is a first-class function value. Its parameter types are unannotated, so
                    // infer them from how the body applies it (spec §blocks).
                    if (annotation != null) {
                        throw functionAnnotation(li);   // an ordinary type does not describe a function
                    }
                    List<Type> paramTypes = inferFnParamTypes(li.name(), li.body(), env, ctx);
                    value = elaborateFunctionValue(li.value(), paramTypes, env, ctx);
                    bindType = value.type();
                } else if (annotation != null) {
                    // the written type is the value's expected type, so an empty collection bound here
                    // takes its element/value type from the annotation rather than staying a bottom
                    value = elaborate(li.value(), env, ctx, annotation);
                    checkLetAnnotation(li, annotation, value.type(), ctx.symbols());
                    bindType = annotation;
                } else {
                    value = elaborate(li.value(), env, ctx);
                    bindType = carriedType(li, value.type(), ctx.symbols());
                }
                if (li.opens() != null) {
                    checkOpens(li, bindType, ctx.symbols());
                }
                // the binding is visible only inside the body, so a sibling branch cannot see it
                Map<String, Type> inner = new HashMap<>(env);
                inner.put(li.name(), bindType);
                Core body = elaborate(li.body(), inner, ctx, expected);
                yield new Core.LetIn(li.name(), value, body, body.type(), li.pos());
            }
            // reached only where a block escapes: it may be passed as an argument, or bound to a
            // `let` and applied, but it is not a value that can be returned or stored, because that
            // would need a runtime closure (spec 12.5)
            // a lambda where a function is expected is that function: the context said what it takes,
            // so nothing has to be read off its applications
            case Ast.Block block when expected instanceof Type.FnOf want ->
                    elaborateFunctionValue(block, want.params(), env, ctx);
            case Ast.Block block -> throw CompileException.of(
                    Diagnostic.of(null, "check.block.notvalue").title("check.block.title")
                            .at(block.pos()).build(),
                    "a block is not a value: it may be passed as an argument or bound to a `let` and "
                            + "applied, but it cannot be returned or stored in a data (spec 12.5)");
            // What the name is was answered when the module's names were resolved; what is left here
            // is its type. A binding is looked up, a unit data is its own value (spec 8.4), and
            // anything else is not a value — reported below under the name that was written.
            case Ast.Var v -> switch (v.denotes()) {
                case null -> throw new IllegalStateException(
                        "`" + v.name() + "` reached the check unresolved, at " + v.pos());
                // A binding with no type here is not a naming question: an inference probe types a
                // body before the binding it asks about has one, and reads the report to find out.
                case ValueName.Local _ when env.get(v.name()) != null ->
                        new Core.Var(v.name(), env.get(v.name()), v.pos());
                case ValueName.OfType named
                        when ctx.symbols().get(named.type()) instanceof Ast.UnitData ->
                        new Core.Var(v.name(), Type.ref(named.type()), v.pos());
                // `None` where a `?` field is being given a value: the empty optional (spec 7.3).
                // What puts it here is the field, which the context says (ADR-0011) — not the expected
                // type, since a model may name `Option<T>` where it reads one and an expectation would
                // then license making one anywhere the name is written (issue #202).
                case ValueName.Builtin b when b.name().equals("None")
                        && ctx.makingAnOptional() && expected instanceof Type.OptionOf ->
                        new Core.OptionNone(expected, v.pos());
                default -> throw notAValue(v, env);
            };
            case Ast.FieldAccess fa -> elaborateFieldAccess(fa, env, ctx);
            case Ast.Call call -> CallElaborator.elaborateCall(call, env, ctx, expected);
            case Ast.Binary bin -> BinaryElaborator.elaborateBinary(bin, env, ctx);
            case Ast.NewData nd -> {
                Ast.Name built = nd.typeName();
                if (built.denotes().isUnresolved()) {
                    throw new Unanswerable(nd.pos());
                }
                if (!(ctx.symbols().get(built.denotes()) instanceof Ast.Data owner)) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.construct.no").title("check.construct.title")
                                    .at(nd.pos(), built.written().length()).args(built.written()).build(),
                            "cannot construct `" + built.written() + "`");
                }
                // by here every spread names a binding in force: a value spread was bound ahead of
                // the construction when it was inlined, so Core reads the name it copies
                List<String> spreads = new ArrayList<>();
                for (Ast.ValueRef s : nd.spreads()) {
                    spreads.add(s.bare());
                }
                List<Core.FieldInit> inits = DataChecker.checkConstruction(built.written(), nd.inits(),
                        spreads, nd.pos(), TypeOps.fieldTypes(owner, ctx.symbols()), env, ctx);
                yield new Core.NewData(built.denotes(), inits, spreads,
                        Type.ref(built.denotes()), nd.pos());
            }
            case Ast.Match m -> MatchElaborator.elaborateMatch(m, env, ctx, expected);
            case Ast.If iff -> {
                Core cond = requireTyped(iff.cond(), Type.BOOL, env, ctx, "if condition");
                // Each branch is lifted before the join, so a field taking `T?` can be given a value
                // on one side and `None` on the other and still have one type (spec 7.3).
                Core then = liftIntoOption(elaborate(iff.then(), env, ctx, expected), expected,
                        ctx.symbols());
                Core els = liftIntoOption(elaborate(iff.els(), env, ctx, expected), expected,
                        ctx.symbols());
                Type tt = then.type();
                Type et = els.type();
                Type joined = TypeOps.join(tt, et);
                if (joined != null) {
                    yield new Core.If(cond, then, els, joined, iff.pos());
                }
                throw CompileException.of(
                        Diagnostic.of(null, "check.if.msg")
                                .title("check.if.title")
                                .at(iff.pos(), 2)
                                .secondary(Region.ofWidth(iff.then().pos(), width(iff.then())),
                                        "check.if.then", Type.show(tt))
                                .secondary(Region.ofWidth(iff.els().pos(), width(iff.els())),
                                        "check.if.else", Type.show(et))
                                .hint("check.if.hint")
                                .build(),
                        "if branches disagree: " + tt + " vs " + et);
            }
            case Ast.IfConstructed ic -> {
                Core built = elaborate(ic.construct(), env, ctx);
                if (!(built instanceof Core.NewData construct)) {
                    throw CompileException.of(
                            Diagnostic.of("E2012", "check.attempt.notconstruction")
                                    .title("check.attempt.title")
                                    .at(ic.construct().pos(), width(ic.construct()))
                                    .hint("check.attempt.notconstruction.hint")
                                    .build(),
                            "`as` attempts a construction, and this is not one");
                }
                // What decides the branch is the invariant, so a type with none has no failing side
                // and the else value could never be reached. Reported rather than compiled into a
                // branch that is not one — the same call a unit data's forbidden invariant makes.
                if (!DataChecker.isInvariantBearing(construct.typeName(), ctx.symbols())) {
                    throw CompileException.of(
                            Diagnostic.of("E2013", "check.attempt.noinvariant")
                                    .title("check.attempt.title")
                                    .at(ic.construct().pos(), width(ic.construct()))
                                    .args(construct.typeName().name())
                                    .hint("check.attempt.noinvariant.hint")
                                    .build(),
                            "`" + construct.typeName().name() + "` has no invariant to attempt");
                }
                // The binder names the built value, so the success branch reads it at the data's own
                // type — with the invariant established, which is why the discharge check may seed it.
                Map<String, Type> inner = new HashMap<>(env);
                inner.put(ic.binder(), construct.type());
                Core then = liftIntoOption(elaborate(ic.then(), inner, ctx, expected), expected,
                        ctx.symbols());
                Core els = liftIntoOption(elaborate(ic.els(), env, ctx, expected), expected,
                        ctx.symbols());
                Type joined = TypeOps.join(then.type(), els.type());
                if (joined == null) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.if.msg")
                                    .title("check.if.title")
                                    .at(ic.pos(), 2)
                                    .secondary(Region.ofWidth(ic.then().pos(), width(ic.then())),
                                            "check.if.then", Type.show(then.type()))
                                    .secondary(Region.ofWidth(ic.els().pos(), width(ic.els())),
                                            "check.if.else", Type.show(els.type()))
                                    .hint("check.if.hint")
                                    .build(),
                            "if branches disagree: " + then.type() + " vs " + els.type());
                }
                yield new Core.IfConstructed(construct, ic.binder(), then, els, joined, ic.pos());
            }
            case Ast.ListLit lit -> {
                if (lit.elements().isEmpty()) {
                    // `[]`: element type fixed by context (ADR-0028); adopt an expected list type
                    yield new Core.ListLit(List.of(),
                            expected instanceof Type.ListOf le ? le : Type.EMPTY_LIST, lit.pos());
                }
                List<Core> elements = new ArrayList<>();
                Type elem = null;
                // an expected list type reaches each element, so a list of functions says what its
                // elements take without every one of them being annotated
                Type want = expected instanceof Type.ListOf le ? le.element() : null;
                for (Ast.Expr el : lit.elements()) {
                    Core c = elaborate(el, env, ctx, want);
                    elements.add(c);
                    elem = elem == null ? c.type() : BottomInfer.unifyElem(elem, c.type(), lit.pos());
                }
                yield new Core.ListLit(elements, Type.list(elem), lit.pos());
            }
            case Ast.ListComp comp -> {
                // A comprehension never reaches the backend: the Lower stage rewrites it to an `if`
                // before a body is emitted, and the codec emitters desugar the expression they hold
                // before elaborating it. It still types here, on the pre-lowering paths (a helper's
                // standalone check), so the node produced is a type carrier, not something to emit.
                for (Ast.Expr g : comp.guards()) {
                    requireType(g, Type.BOOL, env, ctx, "guard of a comprehension");
                }
                Core element = elaborate(comp.element(), env, ctx);
                yield new Core.ListLit(List.of(element), Type.list(element.type()), comp.pos());
            }
        };
    }

    /** Elaborates {@code e} and checks it against {@code expected}, returning its Core. The check is
     * bottom-up, as {@link #requireType} is: the expected type is not pushed into the expression. */
    static Core requireTyped(Ast.Expr e, Type expected, Map<String, Type> env, CheckContext ctx, String what) {
        Core c = elaborate(e, env, ctx);
        requireType(e, c.type(), expected, ctx.symbols(), what);
        return c;
    }


    static Core elaborateFieldAccess(Ast.FieldAccess fa, Map<String, Type> env, CheckContext ctx) {
        Core targetCore = elaborate(fa.target(), env, ctx);
        Type target = targetCore.type();
        if (target instanceof Type.Ref ref && ctx.symbols().get(ref.name()) instanceof Ast.Data owner) {
            Type ft = TypeOps.fieldType(owner, fa.field(), ctx.symbols());
            if (ft != null) {
                return new Core.FieldAccess(targetCore, fa.field(), ft, fa.pos());
            }
        }
        List<TypeName> cases = TypeOps.sumCases(target, ctx.symbols());
        if (cases != null) {
            // A field every case spreads is the sum's own: the sharing is nominal, and the generated
            // sealed interface declares the accessor its cases already carry (issue #160). Only a
            // named sum, whose interface this compile emits — an anonymous union's cases are not
            // written together, so nothing declares their shared part.
            if (target instanceof Type.Ref ref && ctx.symbols().get(ref.name()) instanceof Ast.SumData) {
                Type shared = TypeOps.commonSpreadFields(cases, ctx.symbols()).get(fa.field());
                if (shared != null) {
                    return new Core.FieldAccess(targetCore, fa.field(), shared, fa.pos());
                }
            }
            // A sum carries no fields of its own — its cases do, and which case it is is not known
            // until it is opened. Saying that is the difference between "this value has no such
            // field" and "read it in each case", which is what the author has to write.
            List<String> without = new ArrayList<>();
            for (TypeName c : cases) {
                if (!(ctx.symbols().get(c) instanceof Ast.Data cd)
                        || !TypeOps.hasField(cd, fa.field(), ctx.symbols())) {
                    without.add(c.name());
                }
            }
            Diagnostic.Builder d = Diagnostic.of(null, "check.access.sum")
                    .title("check.type.mismatch.title")
                    .at(fa.pos(), fa.field().length()).args(fa.field(), Type.show(target));
            if (!without.isEmpty()) {
                d = d.hint("check.access.sum.missing", fa.field(), String.join(", ", without));
            } else if (target instanceof Type.Ref) {
                // Every case has the field and the read still fails, so what is missing is the shared
                // spread. Without saying so the author reads "a sum has no fields" while looking at
                // the field in every case.
                d = d.hint("check.access.sum.unshared", fa.field());
            }
            throw CompileException.of(d.build(),
                    "cannot read a field `" + fa.field() + "` on the sum `" + Type.show(target)
                            + "`: a sum has no fields of its own; open it with `match`");
        }
        throw CompileException.of(
                Diagnostic.of(null, "check.access").title("check.type.mismatch.title")
                        .at(fa.pos(), fa.field().length()).args(fa.field()).build(),
                "cannot access field `" + fa.field() + "` on this value");
    }

    /**
     * Types a block argument, binding its parameters to {@code paramTypes} (spec 12.5).
     *
     * <p>The parameters are visible only inside the block's body, and its requirement set is
     * whatever it calls — which flows outward into the enclosing behavior's, so nothing about
     * requirements has to be written down (spec 29).
     */
    /**
     * Resolves the accumulator type for one function argument (a fold's step) of a helper call,
     * updating {@code bind}. The step is first typed at the accumulator the value arguments fixed —
     * the seed's type, which may be a narrow case. That type stands when the step is a fixpoint there
     * (it reads the seed's fields and returns the same case). Only when the narrow case does not type
     * (the step matches on the accumulator, which needs its sum) or is not a fixpoint (the step grows
     * the accumulator into its sum) is the accumulator widened to the sum that case belongs to, and the
     * step re-typed there. An empty-collection seed's bottom is refined from the block's result along
     * the way. Shared by the checker's call typing and the backend's step materialization, so the two
     * resolve identically.
     */
    public static Core resolveStepBinding(String fnName, Type.FnOf declaredStep, Ast.Expr stepArg,
                                          Map<String, Type> bind, Map<String, Type> env, CheckContext ctx) {
        Type.FnOf narrow = (Type.FnOf) TypeOps.substitute(declaredStep, bind);
        Core narrowCore = null;
        Type narrowGot = null;
        CompileException narrowFailed = null;
        try {
            narrowCore = elaborateBlockArg(fnName, stepArg, narrow.params(), env, ctx);
            narrowGot = ((Type.FnOf) narrowCore.type()).result();
        } catch (CompileException e) {
            narrowFailed = e;
        }
        if (narrowGot != null) {
            BottomInfer.refineBottom(declaredStep.result(), narrowGot, bind);
            Type want = TypeOps.substitute(declaredStep.result(), bind);
            if (want instanceof Type.Var || TypeOps.assignable(narrowGot, want, ctx.symbols())) {
                return narrowCore;   // the narrow accumulator is a fixpoint
            }
        }
        // The step matches on, or grows the accumulator into, the sum the seed's case belongs to.
        if (declaredStep.result() instanceof Type.Var accVar) {
            Type sum = TypeOps.enclosingSum(TypeOps.substitute(declaredStep.result(), bind), ctx.symbols());
            if (sum != null) {
                Map<String, Type> widened = new HashMap<>(bind);
                widened.put(accVar.name(), sum);
                Core widenedCore = elaborateBlockArg(fnName, stepArg,
                        ((Type.FnOf) TypeOps.substitute(declaredStep, widened)).params(), env, ctx);
                Type got = ((Type.FnOf) widenedCore.type()).result();
                if (TypeOps.assignable(got, sum, ctx.symbols())) {
                    bind.put(accVar.name(), sum);
                    return widenedCore;   // the step is emitted at the widened accumulator
                }
            }
        }
        if (narrowGot == null) {
            throw narrowFailed;   // the narrow type errored and there was no sum to fall back to
        }
        throw CompileException.of(
                Diagnostic.of(null, "check.fn.argtype").title("check.fn.title")
                        .at(stepArg.pos()).args(fnName, Type.show(narrowGot),
                                Type.show(TypeOps.substitute(declaredStep.result(), bind))).build(),
                "the step of " + fnName + " returns " + Type.show(narrowGot)
                        + ", but the accumulator is " + Type.show(TypeOps.substitute(declaredStep.result(), bind)));
    }

    /** Elaborates a block argument at {@code paramTypes}; the node it returns carries the
     * {@link Type.FnOf} of the block — the parameter types the call fixed, and the body's result. */
    static Core elaborateBlockArg(String fnName, Ast.Expr arg, List<Type> paramTypes,
                                  Map<String, Type> env, CheckContext ctx) {
        if (!(arg instanceof Ast.Block block)) {
            // a function-typed value — a helper's function parameter (spec §fn-declaration) —
            // stands in for a block: check its shape and yield its result type.
            Core value = elaborate(arg, env, ctx);
            if (value.type() instanceof Type.FnOf fn) {
                if (fn.params().size() != paramTypes.size()) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.fn.callarity").title("check.fn.title")
                                    .at(arg.pos()).args(fnName, paramTypes.size(), fn.params().size())
                                    .build(),
                            fnName + " calls its function with " + paramTypes.size()
                                    + " argument(s), but it takes " + fn.params().size());
                }
                for (int i = 0; i < paramTypes.size(); i++) {
                    if (!TypeOps.assignable(paramTypes.get(i), fn.params().get(i), ctx.symbols())) {
                        throw CompileException.of(
                                Diagnostic.of(null, "check.fn.argtype").title("check.fn.title")
                                        .at(arg.pos()).args(fnName, Type.show(paramTypes.get(i)),
                                                Type.show(fn.params().get(i))).build(),
                                fnName + "'s element type " + paramTypes.get(i)
                                        + " is not acceptable to the function, which takes "
                                        + fn.params().get(i));
                    }
                }
                return value;
            }
            throw CompileException.of(
                    Diagnostic.of(null, "check.fn.expectsblock").title("check.fn.title")
                            .at(arg.pos()).args(fnName).build(),
                    fnName + " expects a block, e.g. `" + fnName
                            + "((acc, x) -> ..., seed, xs)` (spec 12.5)");
        }
        if (block.params().size() != paramTypes.size()) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.fn.blockarity").title("check.fn.title")
                            .at(block.pos()).args(paramTypes.size(), block.params().size()).build(),
                    "this block takes " + paramTypes.size() + " parameter(s), got "
                            + block.params().size());
        }
        Map<String, Type> inner = new HashMap<>(env);
        for (int i = 0; i < paramTypes.size(); i++) {
            inner.put(block.params().get(i), paramTypes.get(i));
        }
        Core body = elaborate(block.body(), inner, ctx);
        return new Core.Block(block.params(), body, Type.fn(paramTypes, body.type()), block.pos());
    }

    /** Whether an expression bound to a {@code let} is a function value: a lambda, or an {@code if}
     * whose branches are functions. Such a value cannot be inlined (the inliner leaves it), so it
     * becomes a first-class {@code Fn} (spec §blocks). */
    public static boolean producesFunction(Ast.Expr e) {
        return switch (e) {
            case Ast.Block _ -> true;
            case Ast.If iff -> producesFunction(iff.then()) || producesFunction(iff.els());
            // a lambda returned under its capture bindings, e.g. inlining `adder(5)` leaves
            // `let $n = 5 in (x) -> x + $n` (spec §blocks)
            case Ast.LetIn li -> producesFunction(li.body());
            default -> false;
        };
    }

    /** The type a source annotation declares on a binding ({@code let x: T = e}), or null when the
     * binding carries none. Read wherever a binding's type is needed, so the annotation and the
     * inference, the checker and the backend cannot drift apart. */
    /**
     * A constructor pattern outside a {@code match} — {@code let Tags(xs) = t}, a parameter written
     * as {@code (Tags(xs))}. Two things have to hold, and neither has anything standing behind it
     * here: a {@code match} arm's name is one of the scrutinee's cases, which the exhaustiveness
     * pass has already established, while a binding names a type on its own authority. So the name
     * MUST be a newtype — a product has fields to read by name and a sum has arms, neither of which
     * a binding opens — and the value MUST be of that very type, or the pattern claims a shape the
     * value does not have and {@code .value} would be read off the wrong nominal type.
     */
    private static void checkOpens(Ast.LetIn li, Type valueType, Symbols symbols) {
        String opened = li.opens().written();
        TypeName layer = li.opens().denotes();
        if (TypeOps.newtypeInner(layer, symbols) == null) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.open.notnewtype").title("check.open.title")
                            .at(li.pos()).args(opened)
                            .hint("check.open.notnewtype.hint").build(),
                    "`" + opened + "` is not a newtype, so a binding cannot open it with `"
                            + opened + "(...)`; a value that may or may not have a shape is opened"
                            + " with `match`");
        }
        // compared as types, not as the text of a name: a type is reachable through the module that
        // declares it, so `probe.a.Tags` and an imported bare `Tags` are the one type
        if (!(valueType instanceof Type.Ref r) || !r.name().equals(layer)) {
            String shown = layer.name();
            String actual = Type.show(valueType);
            throw CompileException.of(
                    Diagnostic.of(null, "check.open.mismatch").title("check.open.title")
                            .at(li.pos()).args(shown, actual)
                            .diff(actual, shown).build(),
                    "this pattern opens `" + shown + "`, but the value is `" + actual + "`");
        }
    }

    static Type annotatedType(Ast.LetIn li, Symbols symbols) {
        return li.annotation() == null ? null : TypeOps.successType(li.annotation(), symbols);
    }

    /**
     * A local binding's written type must be the type of its value (spec 16.1). A declared type that
     * the value does not have is an error rather than a comment the checker ignores — the same rule a
     * helper's declared return type follows.
     */
    static void checkLetAnnotation(Ast.LetIn li, Type declared, Type valueType,
                                           Symbols symbols) {
        if (TypeOps.assignable(valueType, declared, symbols)) {
            return;
        }
        throw CompileException.of(
                Diagnostic.of(null, "check.let.annotation").title("check.type.mismatch.title")
                        .at(li.pos()).args(li.name(), Type.show(declared), Type.show(valueType))
                        .diff(Type.show(valueType, declared), Type.show(declared, valueType)).build(),
                "the binding `" + li.name() + "` declares " + Type.show(declared)
                        + " but its value is " + Type.show(valueType));
    }

    /**
     * The type to bind an un-annotated binding at. A binding carrying an inlined helper's declared
     * parameter type keeps that type when it is a sum: a case argument widens to its sum (spec 8.3),
     * so a {@code match} in the body still sees the sum rather than the argument's specific case.
     * Other declared types (a type variable in a generic prelude helper, a record, a list) are left to
     * the argument's own type, which monomorphisation and the call-site check already handle.
     */
    static Type carriedType(Ast.LetIn li, Type valueType, Symbols symbols) {
        if (li.declaredType() instanceof Ast.RetType rt) {
            Type declared = TypeOps.resolveParamType(rt, symbols);
            if (TypeOps.isSumType(declared, symbols) && TypeOps.assignable(valueType, declared, symbols)) {
                return declared;
            }
        }
        return valueType;
    }

    /** {@code let f: T = <function>} — a binding whose value is a function takes no annotation, because
     * a function type may be written only in a helper's parameter (spec 13.1) and no ordinary type
     * describes a function. Raised from the surface check below and from the value path, so the two
     * shapes a function binding takes (a bare lambda, one an {@code if} chooses) read the same. */
    static CompileException functionAnnotation(Ast.LetIn li) {
        return CompileException.of(
                Diagnostic.of(null, "check.fn.annotation").title("check.fn.title")
                        .at(li.pos()).args(li.name()).hint("check.fn.annotation.hint").build(),
                "the binding `" + li.name() + "` is a function, so it takes no annotation: a function"
                        + " type may be written only in a helper's parameter (spec 13.1)");
    }

    /**
     * Checks an annotation on a lambda binding, read on the surface body: lowering expands such a
     * binding away at its applications, so by the time the body is checked the annotation is gone.
     * What it states is still held against the lambda here — a function type, of the arity the lambda
     * binds. An ordinary type does not describe a lambda at all.
     */
    static void checkAnnotatedLambdaBindings(Ast.Expr e, Symbols symbols) {
        if (e instanceof Ast.LetIn li && li.annotation() != null
                && li.value() instanceof Ast.Block lambda) {
            Ast.FnType declared = li.annotation().asFn();
            if (declared == null) {
                throw functionAnnotation(li);
            }
            if (declared.params().size() != lambda.params().size()) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.fn.lambdaarity").title("check.fn.title")
                                .at(lambda.pos())
                                .args(lambda.params().size(), declared.params().size()).build(),
                        "this lambda takes " + lambda.params().size()
                                + " parameter(s) but its type states " + declared.params().size());
            }
        }
        TypeChecker.forEachChild(e, sub -> checkAnnotatedLambdaBindings(sub, symbols));
    }

    /** A function value that could not be inlined away and so becomes a first-class {@code Fn}: a
     * function chosen at runtime by an {@code if} (spec §blocks). A bare lambda is not here — it is
     * either inlined at its application or, if it escapes, reported as "a block is not a value". */
    public static boolean isFunctionSelection(Ast.Expr e) {
        return !(e instanceof Ast.Block) && producesFunction(e);
    }


    /** Infers a let-bound function's parameter types from how the body applies it: every
     * {@code f(args)} in the body must agree on the argument types (spec §blocks). A function that
     * is never applied cannot have its type inferred. */
    static List<Type> inferFnParamTypes(String name, Ast.Expr body, Map<String, Type> env,
                                                CheckContext ctx) {
        List<List<Type>> uses = new ArrayList<>();
        collectApplications(name, body, env, ctx, uses, Set.of());
        if (uses.isEmpty()) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.fn.noinfer").title("check.fn.title")
                            .at(body.pos()).args(name).build(),
                    "cannot infer the type of the function `" + name + "`: write its type (`let "
                            + name + ": (Int) -> Bool = ...`), or apply it in this scope so the"
                            + " parameter types can be read off the application");
        }
        List<Type> first = uses.get(0);
        for (List<Type> u : uses) {
            if (!u.equals(first)) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.fn.difftypes").title("check.fn.title")
                                .at(body.pos()).args(name, first.toString(), u.toString()).build(),
                        "the function `" + name + "` is applied with different argument types: "
                                + first + " vs " + u);
            }
        }
        return first;
    }

    /**
     * Collects the argument-type lists of every application {@code name(args)} in {@code e} that this
     * scope can read.
     *
     * <p>{@code inner} names what a binder below this point has introduced — a lambda's parameters, a
     * {@code let}, a {@code match} arm's binding. An application whose arguments reach one of those is
     * not in this scope and says nothing about the parameter types here, which is exactly where a
     * combinator's own expansion puts the application. It is skipped rather than typed: typing it
     * would report a name that is bound, only not here, and the report would name what the expansion
     * renamed it to.
     *
     * <p>Every other application is typed against {@code env}, so a mistake inside its arguments is
     * still reported as the mistake it is.
     */
    static void collectApplications(String name, Ast.Expr e, Map<String, Type> env,
                                            CheckContext ctx, List<List<Type>> out,
                                            Set<String> inner) {
        if (e instanceof Ast.Call call && call.fn().equals(name)
                && call.args().stream().noneMatch(a -> reaches(a, inner))) {
            List<Type> argTypes = new ArrayList<>();
            for (Ast.Expr a : call.args()) {
                argTypes.add(typeOf(a, env, ctx));
            }
            out.add(argTypes);
        }
        switch (e) {
            case Ast.Block b -> collectApplications(name, b.body(), env, ctx, out,
                    with(inner, b.params()));
            case Ast.LetIn li -> {
                collectApplications(name, li.value(), env, ctx, out, inner);
                collectApplications(name, li.body(), env, ctx, out, with(inner, List.of(li.name())));
            }
            case Ast.IfConstructed ic -> {
                collectApplications(name, ic.construct(), env, ctx, out, inner);
                collectApplications(name, ic.then(), env, ctx, out,
                        with(inner, List.of(ic.binder())));
                collectApplications(name, ic.els(), env, ctx, out, inner);
            }
            case Ast.Match m -> {
                collectApplications(name, m.scrutinee(), env, ctx, out, inner);
                for (Ast.Case c : m.cases()) {
                    collectApplications(name, c.body(), env, ctx, out,
                            c.binding() == null ? inner : with(inner, List.of(c.binding())));
                }
            }
            default -> TypeChecker.forEachChild(e,
                    sub -> collectApplications(name, sub, env, ctx, out, inner));
        }
    }

    private static Set<String> with(Set<String> names, List<String> added) {
        if (added.isEmpty()) {
            return names;
        }
        Set<String> out = new HashSet<>(names);
        out.addAll(added);
        return out;
    }

    /**
     * Whether {@code e} reads a name a binder below the inference point introduced — that is, whether
     * its <em>free</em> variables meet {@code inner}. A binder inside {@code e} takes its own name off
     * the set for what it covers, so a name rebound there is that binding's and not the outer one's:
     * {@code f(match m with | Some y -> y | None -> 0)} does not read an enclosing {@code y}, and
     * whether the case happens to spell its binding {@code y} or {@code z} decides nothing.
     */
    private static boolean reaches(Ast.Expr e, Set<String> inner) {
        if (inner.isEmpty()) {
            return false;
        }
        if (e instanceof Ast.Var v && inner.contains(v.name())) {
            return true;
        }
        if (e instanceof Ast.Call c && inner.contains(c.fn())) {
            return true;
        }
        return switch (e) {
            case Ast.Block b -> reaches(b.body(), without(inner, b.params()));
            case Ast.LetIn li -> reaches(li.value(), inner)
                    || reaches(li.body(), without(inner, List.of(li.name())));
            case Ast.IfConstructed ic -> reaches(ic.construct(), inner)
                    || reaches(ic.then(), without(inner, List.of(ic.binder())))
                    || reaches(ic.els(), inner);
            case Ast.Match m -> {
                if (reaches(m.scrutinee(), inner)) {
                    yield true;
                }
                for (Ast.Case c : m.cases()) {
                    Set<String> arm = c.binding() == null
                            ? inner : without(inner, List.of(c.binding()));
                    if (reaches(c.body(), arm)) {
                        yield true;
                    }
                }
                yield false;
            }
            default -> {
                boolean[] found = {false};
                TypeChecker.forEachChild(e, sub -> found[0] |= reaches(sub, inner));
                yield found[0];
            }
        };
    }

    private static Set<String> without(Set<String> names, List<String> removed) {
        if (names.isEmpty() || removed.isEmpty()) {
            return names;
        }
        Set<String> out = new HashSet<>(names);
        out.removeAll(removed);
        return out;
    }

    /** Types a function value against inferred parameter types: a lambda binds its parameters and
     * yields {@code FnOf(params, resultOfBody)}; an {@code if} requires both branches to be the same
     * function type (spec §blocks). */
    static Core elaborateFunctionValue(Ast.Expr value, List<Type> paramTypes, Map<String, Type> env,
                                          CheckContext ctx) {
        return switch (value) {
            case Ast.Block b -> {
                if (b.params().size() != paramTypes.size()) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.fn.lambdaarity").title("check.fn.title")
                                    .at(b.pos()).args(b.params().size(), paramTypes.size()).build(),
                            "this lambda takes " + b.params().size() + " parameter(s) but is applied with "
                                    + paramTypes.size());
                }
                Map<String, Type> inner = new HashMap<>(env);
                for (int i = 0; i < paramTypes.size(); i++) {
                    inner.put(b.params().get(i), paramTypes.get(i));
                }
                Core body = elaborate(b.body(), inner, ctx);
                yield new Core.Block(b.params(), body, Type.fn(paramTypes, body.type()), b.pos());
            }
            case Ast.If iff -> {
                Core cond = requireTyped(iff.cond(), Type.BOOL, env, ctx, "if condition");
                Core then = elaborateFunctionValue(iff.then(), paramTypes, env, ctx);
                Core els = elaborateFunctionValue(iff.els(), paramTypes, env, ctx);
                Type t = then.type();
                Type f = els.type();
                if (!t.equals(f)) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.fn.branchtypes").title("check.fn.title")
                                    .at(iff.pos(), 2).args(Type.show(t), Type.show(f)).build(),
                            "the two branches produce different function types: " + t + " vs " + f);
                }
                yield new Core.If(cond, then, els, t, iff.pos());
            }
            case Ast.LetIn li -> {
                // a capture binding around the function (e.g. `let $n = 5 in (x) -> x + $n`)
                Core bound = elaborate(li.value(), env, ctx);
                Map<String, Type> inner = new HashMap<>(env);
                inner.put(li.name(), bound.type());
                Core body = elaborateFunctionValue(li.body(), paramTypes, inner, ctx);
                yield new Core.LetIn(li.name(), bound, body, body.type(), li.pos());
            }
            default -> elaborate(value, env, ctx);
        };
    }

    /** The built-in rounding modes (spec 18.3), each a bare identifier resolving to a
     * {@code java.math.RoundingMode} — like {@code None}, a built-in value, not a data (spec 8.4). */
    public static final Set<String> ROUNDING_MODES = Set.of(
            "HALF_UP", "HALF_EVEN", "HALF_DOWN", "UP", "DOWN", "CEILING", "FLOOR");

    /** Built-in values written as bare identifiers ({@code None}, the rounding modes): a binding may
     * not take one of these names, because it would shadow the built-in and make it unreachable. */
    static final Set<String> BUILTIN_VALUES = builtinValues();

    static Set<String> builtinValues() {
        Set<String> s = new HashSet<>(ROUNDING_MODES);
        s.add("None");
        return Set.copyOf(s);
    }

    static void rejectBuiltinShadow(String name, SourcePos pos) {
        if (BUILTIN_VALUES.contains(name)) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.builtin.shadow").title("check.reserved.title")
                            .at(pos, name.length()).args(name).build(),
                    "`" + name + "` is a built-in value and cannot be used as a binding name — it would"
                            + " shadow the built-in; choose another name");
        }
    }

    /** Rejects any binder in {@code e} — a {@code let}, {@code match} binding, or lambda parameter —
     * that takes a built-in value's name. */
    static void rejectBuiltinShadowing(Ast.Expr e) {
        switch (e) {
            case Ast.LetIn li -> {
                rejectBuiltinShadow(li.name(), li.pos());
                rejectBuiltinShadowing(li.value());
                rejectBuiltinShadowing(li.body());
            }
            case Ast.Block b -> {
                for (String p : b.params()) {
                    rejectBuiltinShadow(p, b.pos());
                }
                rejectBuiltinShadowing(b.body());
            }
            case Ast.Match m -> {
                rejectBuiltinShadowing(m.scrutinee());
                for (Ast.Case c : m.cases()) {
                    if (c.binding() != null) {
                        rejectBuiltinShadow(c.binding(), c.pos());
                    }
                    rejectBuiltinShadowing(c.body());
                }
            }
            default -> TypeChecker.forEachChild(e, Elaborator::rejectBuiltinShadowing);
        }
    }

    static void requireType(Ast.Expr e, Type expected, Map<String, Type> env, CheckContext ctx, String what) {
        requireType(e, typeOf(e, env, ctx), expected, ctx.symbols(), what);
    }

    /** As {@link #requireType(Ast.Expr, Type, Map, Ast.Data, Map, Map, String)}, but with the
     * operand's type already computed — a caller that has typed {@code e} does not re-type its
     * subtree. */
    static void requireType(Ast.Expr e, Type actual, Type expected,
                                    Symbols symbols, String what) {
        if (!TypeOps.assignable(actual, expected, symbols)) {   // a case widens to its sum (spec 8.3)
            throw CompileException.of(
                    Diagnostic.of(null, "check.type.mismatch.msg")
                            .title("check.type.mismatch.title")
                            .at(e.pos(), width(e))
                            .args(what)
                            .diff(Type.show(actual, expected), Type.show(expected, actual))
                            .hint("check.type.mismatch.hint")
                            .build(),
                    what + " must be " + expected + " but is " + actual);
        }
    }

    /**
     * Wraps a value being given to a {@code ?} field, so {@code Out { note = n }} puts {@code n}
     * where an optional is asked for (spec 7.3). Construction is the one place this happens: an
     * expected optional only ever arrives from a field's own type, because nowhere else in a model
     * can {@code T?} be written (ADR-0011) — a lambda handed to a stdlib combinator is typed with no
     * expected type at all ({@code HelperTyping}), so a step for {@code List.filterMap} still has to
     * answer an optional of its own. That keeps this a rule about building a data rather than a
     * coercion applied wherever two shapes nearly line up.
     *
     * <p>A value that is already the optional — read from another field, or {@code None} — is
     * returned untouched, and so is one whose type has nothing to do with the field, which the
     * caller then reports as the mismatch it is.
     */
    static Core liftIntoOption(Core value, Type expected, Symbols symbols) {
        if (!(expected instanceof Type.OptionOf opt)
                || TypeOps.assignable(value.type(), expected, symbols)
                || !TypeOps.assignable(value.type(), opt.element(), symbols)) {
            return value;
        }
        return new Core.OptionSome(value, expected, value.pos());
    }

    /**
     * A name written where a value goes that is not one: an unknown name, a type that is not a unit
     * data, a function named without being applied, or one of Option's cases outside the one place
     * an optional is made.
     */
    private static RuntimeException notAValue(Ast.Var v, Map<String, Type> env) {
        if (v.denotes() instanceof ValueName.Unresolved) {
            // reported where the name was written; this definition has no meaning to work out
            return new Unanswerable(v.pos());
        }
        optionCaseWritten(v.name(), v.pos());
        return CompileException.of(
                Diagnostic.of(null, "check.unknown.name.msg")
                        .title("check.unknown.title")
                        .at(v.pos(), v.name().length())
                        .args(v.name())
                        .suggestion(Suggest.candidate(v.name(), env.keySet()))
                        .build(),
                "unknown identifier `" + v.name() + "`" + Suggest.hint(v.name(), env.keySet()));
    }

    /**
     * Rejects {@code Some} / {@code None} written where no {@code ?} field is being given a value
     * (E1303). Giving a field its value is the one place an optional is made — the wrap is implicit
     * and {@code None} is the empty one (spec 7.3) — and everywhere else an optional is read and
     * passed on. Neither an unknown-name report nor an arbitrary-call report says that, and the
     * latter sent the reader off to write a Java binding, which makes no optional either (issue
     * #166). Patterns do not come through here: {@code | Some v} is matched, not evaluated.
     */
    static void optionCaseWritten(String name, SourcePos pos) {
        boolean some = name.equals("Some");
        if (!some && !name.equals("None")) {
            return;
        }
        throw CompileException.of(
                Diagnostic.of("E1303", some ? "e1303.some" : "e1303.none").title("e1303.title")
                        .at(pos, name.length())
                        .hint(some ? "e1303.some.hint" : "e1303.none.hint").build(),
                some
                        ? "`Some(...)` is not a call: a value written into a `?` field is wrapped for"
                                + " you, and that is the only place an optional is made. Where a `?`"
                                + " field is being given a value, write the value on its own;"
                                + " elsewhere an optional is only read, never made."
                        : "`None` is the empty value of a `?` field, and nothing here is asking for"
                                + " one. Where the model owns the absence, make it a case of its own"
                                + " sum. Absence of that kind does not reach `List.filterMap`, whose"
                                + " step has to answer an optional: use `List.concatMap` over a step"
                                + " answering a list of nought or one.");
    }

    /** A best-effort caret width for {@code e}: the token length when the node is a leaf whose source
     * text is known, otherwise 1. The renderer underlines this many columns from the node's start. */
    static int width(Ast.Expr e) {
        return switch (e) {
            case Ast.Var v -> v.name().length();
            case Ast.StringLit s -> s.value().length() + 2;
            case Ast.IntLit i -> Long.toString(i.value()).length();
            case Ast.BoolLit b -> b.value() ? 4 : 5;
            case Ast.DecimalLit d -> d.value().toPlainString().length() + 1;
            case Ast.FieldAccess fa -> fa.field().length();
            case Ast.Call c -> c.fn().length();
            default -> 1;
        };
    }
}
