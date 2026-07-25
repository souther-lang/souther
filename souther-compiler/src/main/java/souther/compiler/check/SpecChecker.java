package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.core.Core;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Localizable;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourcePos;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * The checks a {@code behavior} and its implementing {@code let} are subject to: that the two agree
 * on inputs and output, that only required behaviors are called from a body, that a stage takes one
 * input, and that an exposed composition declares the output it actually produces.
 */
public final class SpecChecker {

    private SpecChecker() {}

    /**
     * An exposed composition ({@code >->}) behavior must declare its output in the {@code exposing}
     * list ({@code exposing ( name : A | B )}, spec 14.5, ADR-0024), and the declaration must match
     * the inferred output exactly. A far-away change that grows the output then fails here, at the
     * module boundary, instead of reaching separately-compiled consumers unannounced.
     *
     * <p>The requirement applies only to a composition that is explicitly exposed: a module with no
     * {@code exposing} publishes everything with inference intact, and a non-composition behavior
     * states its type at its definition, so a signature on one is rejected.
     */
    static void checkExposedPipeOutputs(Ast.Module module, Set<String> exposed,
            Map<String, Sig> sigs, Map<String, Ast.Def> symbols) {
        Set<String> pipeNames = new HashSet<>();
        for (Ast.BehaviorDef b : module.behaviors()) {
            if (b instanceof Ast.PipeBehavior p) {
                pipeNames.add(p.name());
            }
        }
        // a signature in `exposing` is only meaningful on a composition behavior
        for (String name : module.exposedOutputs().keySet()) {
            if (!pipeNames.contains(name)) {
                throw CompileException.of(
                        Diagnostic.of("E1605", "e1605.notcomposition").at(module.pos()).args(name).build(),
                        "`exposing` gives an output signature to `" + name + "`, which is not a"
                                + " composition (`>->`) behavior; only a composition needs one — every"
                                + " other definition states its type where it is written (spec 14.5)");
            }
        }
        // every exposed composition must declare its output, matching the inferred one
        for (Ast.BehaviorDef b : module.behaviors()) {
            if (!(b instanceof Ast.PipeBehavior pipe) || !exposed.contains(pipe.name())) {
                continue;
            }
            Set<String> inferred = TypeOps.leafCases(sigs.get(pipe.name()).out(), symbols);
            Ast.RetType declared = module.exposedOutputs().get(pipe.name());
            if (declared == null) {
                throw CompileException.of(
                        Diagnostic.of("E1605", "e1605.missing").at(pipe.pos())
                                .args(pipe.name())
                                .hint("e1605.missing.hint", pipe.name(), PipelineSigs.caseList(inferred))
                                .build(),
                        "exposed composition `" + pipe.name() + "` must declare its output in `exposing`"
                                + " (spec 14.5): write `exposing ( " + pipe.name() + " : "
                                + PipelineSigs.caseList(inferred) + " )`");
            }
            Set<String> declaredCases = TypeOps.leafCases(TypeOps.successType(declared, symbols), symbols);
            if (!inferred.equals(declaredCases)) {
                throw CompileException.of(
                        Diagnostic.of("E1604", "e1604.msg").at(pipe.pos())
                                .args(pipe.name(), PipelineSigs.caseList(declaredCases), PipelineSigs.caseList(inferred))
                                .hint("e1604.hint")
                                .build(),
                        "exposed composition `" + pipe.name() + "` declares -> " + PipelineSigs.caseList(declaredCases)
                                + " in `exposing`, but the pipeline produces " + PipelineSigs.caseList(inferred)
                                + ". Update the declared output or handle the case.");
            }
        }
    }

    /**
     * Checks a behavior's {@code fn} implementation against the behavior's declared signature
     * (spec 13.1). The {@code fn}'s parameters are the behavior's inputs followed by its
     * {@code requires} (12.6); the trailing ones name the injection targets in declared order and
     * do not bind values — they resolve as inline calls to those behaviors.
     */
    static Core checkSpecFn(Ast.SpecBehavior spec, Ast.FnDef fn, Ast.Expr inlinedBody,
                                    Map<String, Ast.Def> symbols, Set<String> allBehaviors,
                                    Map<String, ReqSig> reqSigs, HelperInliner inliner,
                                    Map<String, Type> recursiveHelperFns,
                                    Map<String, Set<String>> recHelperConstructs,
                                    List<Diagnostic> warnings) {
        if (fn.declaredReturn() != null) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.impl.noreturn").title("check.impl.title")
                            .at(fn.pos()).args(fn.name(), spec.name()).build(),
                    "`let " + fn.name() + "` implements `behavior " + spec.name()
                            + "`, so its return type comes from the behavior — do not declare one"
                            + " (spec 13.1)");
        }
        int nBusiness = spec.params().size();
        int nReq = spec.requires().size();
        if (fn.params().size() != nBusiness + nReq) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.impl.arity").title("check.impl.title")
                            .at(fn.pos()).args(fn.name(), fn.params().size(), spec.name(), nBusiness, nReq)
                            .build(),
                    "`let " + fn.name() + "` takes " + fn.params().size()
                            + " parameter(s) but `behavior " + spec.name() + "` has " + nBusiness
                            + " input(s)" + (nReq == 0 ? "" : " plus " + nReq + " requires")
                            + " (spec 13.1)");
        }
        for (Ast.FnParam p : fn.params()) {
            if (p.type() != null) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.impl.noannotate").title("check.impl.title")
                                .at(p.pos()).args(fn.name(), spec.name(), p.name()).build(),
                        "`let " + fn.name() + "` implements `behavior " + spec.name()
                                + "`, so its parameters take their types from it — do not annotate `"
                                + p.name() + "` (spec 13.1)");
            }
        }
        for (int i = 0; i < nReq; i++) {
            String got = fn.params().get(nBusiness + i).name();
            String want = spec.requires().get(i);
            if (!got.equals(want)) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.impl.reqorder").title("check.impl.title")
                                .at(fn.pos()).args(fn.name(), got, want).build(),
                        "`let " + fn.name() + "` parameter `" + got + "` should be `" + want
                                + "`: the `requires` become the trailing parameters in declared order"
                                + " (spec 12.6)");
            }
        }

        Map<String, Type> env = new HashMap<>();
        for (Ast.FnParam p : fn.params()) {
            Elaborator.rejectBuiltinShadow(p.name(), p.pos());
        }
        Elaborator.rejectBuiltinShadowing(fn.body());
        for (int i = 0; i < nBusiness; i++) {
            env.put(fn.params().get(i).name(), TypeOps.successType(spec.params().get(i).type(), symbols));
        }
        Type output = TypeOps.successType(spec.ret(), symbols);
        // recursive helpers this behavior calls resolve through their signatures (spec 13.1); merged
        // only for typing, so construction/requires walks below still see the business params alone.
        Map<String, Type> tenv = new HashMap<>(env);
        tenv.putAll(recursiveHelperFns);
        // Check functions passed to helper parameters (e.g. a combinator's predicate) against their
        // declared types first, so a mismatch names the parameter, not the derivation it expands to.
        // A nested fold reaches `List.foldFrom` inside a block, so its signature must be in scope here.
        HelperTyping.checkFunctionArgs(fn.body(), tenv, symbols, reqSigs, inliner);
        // The body arrives with helper calls already expanded (the Lower stage, ADR-0021): it is
        // checked as one expression, so a helper's constructions and injected calls count toward this
        // behavior's permission and requires — exactly as if the code had been written inline (12.5).
        Ast.Expr body = inlinedBody;
        rejectNonRequiredCalls(body, allBehaviors, reqSigs);

        // push the declared output type into the body so a body that is directly an empty collection
        // (or a construction whose field is one) takes the declared type rather than a bottom
        Core elaboratedBody = Elaborator.elaborate(body, tenv, null, symbols, reqSigs, output);
        Type rt = elaboratedBody.type();
        if (!TypeOps.assignable(rt, output, symbols)) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.behavior.return").title("check.type.mismatch.title")
                            .at(body.pos()).args(spec.name(), Type.show(output), Type.show(rt))
                            .diff(Type.show(rt), Type.show(output)).build(),
                    "behavior `" + spec.name() + "` returns " + output + " but its `let` body is " + rt);
        }

        // One expression (spec 16.4): this single walk sees every construction, including under a
        // desugared `require`.
        Set<String> constructed = new HashSet<>();
        DataChecker.collectConstructs(body, constructed, symbols, new HashSet<>(env.keySet()), recHelperConstructs);
        // `constructs` on an fn-backed behavior is optional: its construction permission is internal
        // (invisible to callers, unlike `requires`), so with the body visible the set can be inferred
        // (ADR-0002). Omit it and inference stands. Declare it and it must match the body exactly —
        // under-declaration is E1002, over-declaration E1006 — so an explicit clause stays a checkable,
        // readable record of what is newly built versus passed through (spec 12.3), the same exact
        // match `requires` gets (E1602/E1603). Injected behaviors still declare it: no body to infer
        // from, and it drives factory generation (spec 13.3).
        if (!spec.constructs().isEmpty()) {
            for (String c : constructed) {
                if (!spec.constructs().contains(c)) {
                    throw CompileException.of(
                            Diagnostic.of("E1002", "e1002.msg").at(spec.pos())
                                    .args(spec.name(), c).hint("e1002.hint").build(),
                            "Behavior `" + spec.name() + "` constructs `" + c
                                    + "` but does not declare `constructs " + c + "`.");
                }
            }
            for (String declared : spec.constructs()) {
                if (!constructed.contains(declared)) {
                    throw CompileException.of(
                            Diagnostic.of("E1006", "e1006.msg").at(spec.pos())
                                    .args(spec.name(), declared).hint("e1006.hint").build(),
                            "Behavior `" + spec.name() + "` declares `constructs " + declared
                                    + "` but never builds " + declared + " — it passes an existing"
                                    + " value through. Remove it from the `constructs` clause.");
                }
            }
        }
        // The requires clause must match what the fn actually calls (spec 12.6): missing -> E1602,
        // extra -> E1603.
        List<String> actual = requiredCalls(body, reqSigs.keySet());
        for (String call : actual) {
            if (!spec.requires().contains(call)) {
                throw CompileException.of(
                        Diagnostic.of("E1602", "e1602.msg").at(spec.pos())
                                .args(fn.name(), call, spec.name()).hint("e1602.hint").build(),
                        "`let " + fn.name() + "` calls `" + call + "`, which has no implementation, but"
                                + " `behavior " + spec.name() + "` does not declare `requires " + call + "`.");
            }
        }
        for (String req : spec.requires()) {
            if (!actual.contains(req)) {
                throw CompileException.of(
                        Diagnostic.of("E1603", "e1603.msg").at(spec.pos())
                                .args(spec.name(), req, fn.name()).hint("e1603.hint").build(),
                        "`behavior " + spec.name() + "` declares `requires " + req + "`, but `let "
                                + fn.name() + "` never calls it. Remove it from the `requires` clause.");
            }
        }
        // Intraprocedural invariant discharge: seed from the input
        // newtypes' invariants, refine along each `require`/`if` guard, and check every construction.
        // A guard-discharged one is silent; an unproven one is a warning (a possible abort); one the
        // guards prove must fail on a reachable path is an error (the path-sensitive generalization of
        // the constant `金額(-5)` check).
        InvariantChecker.Findings inv = InvariantChecker.analyze(body, env, symbols);
        warnings.addAll(inv.warnings());
        if (!inv.errors().isEmpty()) {
            throw inv.errors().get(0);
        }
        return elaboratedBody;
    }

    /**
     * An injected behavior's declared {@code constructs} must each be Java-buildable (spec 13.3):
     * a unit data (the base class hands the implementation a {@code protected} factory) or an
     * exposed data (its {@code decoder} is public). A non-unit, unexposed one is E1305 — Java has
     * no way to mint it.
     */
    /**
     * An anonymous union appears only in a behavior's output; a parameter type is always a single
     * named type, a named sum included (spec 8.6, 12.2). A parameter written as {@code A | B} — a
     * {@code RetType} with more than one case — is rejected: declare {@code data AB = A | B} and take
     * {@code (x: AB)}, so the input has a name the reader and the JVM can hold onto.
     */
    static void rejectAnonymousUnionParams(Ast.SpecBehavior spec) {
        for (Ast.Param p : spec.params()) {
            if (p.type().cases().size() > 1) {
                String union = p.type().cases().stream()
                        .map(Ast.TypeRef::name)
                        .collect(java.util.stream.Collectors.joining(" | "));
                throw CompileException.of(
                        Diagnostic.of(null, "check.param.union").title("check.boundary.title")
                                .at(p.pos(), p.name().length()).args(p.name(), union).build(),
                        "parameter `" + p.name() + "` has an anonymous union type `" + union
                                + "`; a parameter type must be a single named type — declare `data ... = "
                                + union + "` and take that name (spec 8.6, 12.2)");
            }
        }
    }

    /** A tuple is expression-level only (ADR-0036): it has no external representation and cannot
     * cross a decoder/encoder boundary, so it may not be a behavior's input or output. Tuple types in
     * a helper/stdlib signature are fine — they never touch a codec. */
    static void rejectTupleIO(Ast.SpecBehavior spec) {
        for (Ast.Param p : spec.params()) {
            for (Ast.TypeRef c : p.type().cases()) {
                if (refHasTuple(c)) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.param.tuple").title("check.boundary.title")
                                    .at(p.pos(), p.name().length()).args(p.name()).build(),
                            "parameter `" + p.name() + "` is a tuple; a tuple has no external"
                                    + " representation and cannot cross the boundary, so a behavior's"
                                    + " input must be a named data (ADR-0036)");
                }
            }
        }
        for (Ast.TypeRef c : spec.ret().cases()) {
            if (refHasTuple(c)) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.output.tuple").title("check.boundary.title")
                                .at(spec.pos()).args(spec.name()).build(),
                        "behavior `" + spec.name() + "` outputs a tuple; a tuple cannot cross the"
                                + " boundary, so a behavior's output must be a named data or a sum of"
                                + " them (ADR-0036)");
            }
        }
    }

    private static boolean refHasTuple(Ast.TypeRef ref) {
        return ref.isTuple() || (ref.arg() != null && refHasTuple(ref.arg()));
    }

    static boolean containsTuple(Type t) {
        return Type.mentions(t, x -> x instanceof Type.TupleOf);
    }

    static void checkInjectionConstructs(Ast.SpecBehavior spec, Map<String, Ast.Def> symbols,
                                                 boolean exposeAll, Set<String> exposed) {
        for (String c : spec.constructs()) {
            Ast.Def d = symbols.get(c);
            if (d == null || d instanceof Ast.UnitData) {
                continue;   // unknown names are caught elsewhere; a unit has a generated factory
            }
            if (!exposeAll && !exposed.contains(c)) {
                throw CompileException.of(
                        Diagnostic.of("E1305", "e1305.msg").at(spec.pos())
                                .args(spec.name(), c).hint("e1305.hint").build(),
                        "Injected behavior `" + spec.name() + "` declares `constructs " + c + "`, but "
                                + c + " is neither a unit data nor exposed. Java cannot build it: no"
                                + " factory is generated and its decoder is not public. Expose " + c
                                + ", or make it a unit data.");
            }
        }
    }

    /**
     * Every stage after the first takes exactly one input (spec 14.1): {@code >->} hands a single
     * value along.
     *
     * <p>The first stage is not restricted — it consumes the pipeline's own arguments, and the
     * pipeline simply takes what it takes. The spec DSL relies on this
     * (`behavior 却下して差し戻す = 却下する >-> 差し戻す`, where `却下する` reads
     * `事前承認待ち AND 却下者ID`); requiring the whole chain to be single-input would reject the
     * very line 14.1 cites.
     */
    static void checkStagesAreSingleInput(Ast.Module module) {
        Map<String, Integer> arity = new HashMap<>();
        for (Ast.BehaviorDef b : module.behaviors()) {
            if (b instanceof Ast.SpecBehavior spec) {
                arity.put(spec.name(), spec.params().size());
            }
        }
        Map<String, List<String>> pipeStages = PipelineSigs.pipelineStages(module);
        for (Ast.BehaviorDef b : module.behaviors()) {
            if (!(b instanceof Ast.PipeBehavior pipe)) {
                continue;
            }
            // check the flattened stages: a named intermediate splices in its own first stage, which
            // then sits after `>->` and so must be single-input too (spec 14.1, 14.2)
            List<String> stages = PipelineSigs.flattenStages(pipe.stages(), pipeStages, pipe.pos());
            for (int i = 1; i < stages.size(); i++) {
                String stage = stages.get(i);
                Integer n = arity.get(stage);
                if (n != null && n != 1) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.pipe.multiinput").title("check.pipe.title")
                                    .at(pipe.pos()).args(stage, n, pipe.name()).build(),
                            "`" + stage + "` takes " + n + " inputs, so it cannot follow `>->` in `"
                                    + pipe.name() + "`. Every stage after the first takes one input: "
                                    + "call it inline or open the branches with `match` instead "
                                    + "(spec 14.1). Only the first stage may take several.");
                }
            }
        }
    }

    /** The distinct injection targets a fn body calls, in first-seen order. Calls may appear
     * anywhere in an expression (e.g. inline in a record literal), not only bound to a let. */
    public static List<String> requiredCalls(Ast.Expr body, java.util.Set<String> requiredNames) {
        List<String> calls = new java.util.ArrayList<>();
        collectRequiredCalls(body, requiredNames, calls);
        return calls;
    }

    private static void collectRequiredCalls(Ast.Expr e, Set<String> requiredNames, List<String> out) {
        switch (e) {
            case Ast.Call call -> {
                if (requiredNames.contains(call.fn()) && !out.contains(call.fn())) {
                    out.add(call.fn());
                }
                call.args().forEach(a -> collectRequiredCalls(a, requiredNames, out));
            }
            case Ast.NewData nd -> nd.inits().forEach(i -> collectRequiredCalls(i.value(), requiredNames, out));
            case Ast.FieldAccess fa -> collectRequiredCalls(fa.target(), requiredNames, out);
            case Ast.Binary bin -> {
                collectRequiredCalls(bin.left(), requiredNames, out);
                collectRequiredCalls(bin.right(), requiredNames, out);
            }
            case Ast.Match m -> {
                collectRequiredCalls(m.scrutinee(), requiredNames, out);
                m.cases().forEach(c -> collectRequiredCalls(c.body(), requiredNames, out));
            }
            case Ast.If iff -> {
                collectRequiredCalls(iff.cond(), requiredNames, out);
                collectRequiredCalls(iff.then(), requiredNames, out);
                collectRequiredCalls(iff.els(), requiredNames, out);
            }
            case Ast.ListLit lit -> lit.elements().forEach(el -> collectRequiredCalls(el, requiredNames, out));
            case Ast.ListComp comp -> {
                collectRequiredCalls(comp.element(), requiredNames, out);
                comp.guards().forEach(g -> collectRequiredCalls(g, requiredNames, out));
            }
            case Ast.LetIn li -> {
                collectRequiredCalls(li.value(), requiredNames, out);
                collectRequiredCalls(li.body(), requiredNames, out);
            }
            // a block's requirements float out to the behavior that passes it (spec 12.5, 29)
            case Ast.Block block -> collectRequiredCalls(block.body(), requiredNames, out);
            default -> { }
        }
    }

    /**
     * Only required behaviors may be called from a body; other behaviors compose with {@code >->}
     * (spec 14.1). Checked up front so the diagnostic names the rule rather than reporting the
     * behavior as an unknown function.
     */
    private static void rejectNonRequiredCalls(Ast.Expr e, Set<String> allBehaviors,
                                               Map<String, ReqSig> reqSigs) {
        if (e instanceof Ast.Call call && allBehaviors.contains(call.fn())
                && !reqSigs.containsKey(call.fn())) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.call.nonrequired").title("check.impl.title")
                            .at(call.pos(), call.fn().length()).build(),
                    "only required behaviors can be called from a body; compose others with `>->`");
        }
        TypeChecker.forEachChild(e, c -> rejectNonRequiredCalls(c, allBehaviors, reqSigs));
    }

}
