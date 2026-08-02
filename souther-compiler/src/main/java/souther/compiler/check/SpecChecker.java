package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.core.Core;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;
import souther.compiler.types.ValueName;

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
 * on inputs and output, that a {@code depends on} names something with a requirement of its own, that
 * no behavior reaches itself, that a stage takes one input, and that an exposed composition declares
 * the output it actually produces.
 */
public final class SpecChecker {

    private SpecChecker() {}

    /**
     * A behavior does not reach itself (spec {@code [#calling-a-behavior]}, E1608). The edges are
     * calls, {@code depends on} and {@code >->} stages, walked as one graph because a cycle through a
     * mixture of them is the same cycle: a {@code depends on} cycle leaves nothing to build first, and
     * a call cycle does not terminate.
     *
     * <p>Only this module's behaviors are walked. Reaching another module's takes an import, and a
     * cycle of imports is already refused (E1501), so following one here could not close a loop this
     * check has not already seen.
     */
    static void checkBehaviorsDoNotRecurse(Ast.Module module) {
        Set<String> names = new LinkedHashSet<>();
        for (Ast.BehaviorDef b : module.behaviors()) {
            names.add(b.name());
        }
        Map<String, List<String>> edges = new LinkedHashMap<>();
        Map<String, Ast.FnDef> fns = new LinkedHashMap<>();
        for (Ast.FnDef fn : module.fns()) {
            fns.put(fn.name(), fn);
        }
        for (Ast.BehaviorDef b : module.behaviors()) {
            List<String> out = new ArrayList<>();
            switch (b) {
                case Ast.SpecBehavior spec -> {
                    for (Ast.Var req : spec.dependsOn()) {
                        if (names.contains(req.bare()) && !out.contains(req.bare())) {
                            out.add(req.bare());
                        }
                    }
                    Ast.FnDef fn = fns.get(spec.name());
                    if (fn != null) {
                        for (String called : requiredCalls(fn.written(), names)) {
                            if (!out.contains(called)) {
                                out.add(called);
                            }
                        }
                    }
                }
                case Ast.PipeBehavior pipe -> {
                    for (Ast.Var stage : pipe.stages()) {
                        if (names.contains(stage.bare()) && !out.contains(stage.bare())) {
                            out.add(stage.bare());
                        }
                    }
                }
            }
            edges.put(b.name(), out);
        }
        for (Ast.BehaviorDef b : module.behaviors()) {
            List<String> path = new ArrayList<>();
            if (reaches(b.name(), b.name(), edges, path, new HashSet<>())) {
                path.add(b.name());
                throw CompileException.of(
                        Diagnostic.of("E1608", "e1608.msg").title("e1608.title")
                                .at(b.pos()).args(b.name(), String.join(" -> ", path))
                                .hint("e1608.hint", b.name()).build(),
                        "behavior `" + b.name() + "` reaches itself: "
                                + String.join(" -> ", path)
                                + "; a behavior does not recurse, so write the recursion as a helper"
                                + " `let` (spec [#calling-a-behavior])");
            }
        }
    }

    /** Whether {@code target} is reachable from {@code from}, recording the way there in
     *  {@code path}. {@code path} starts with {@code from} and ends at the last step before
     *  {@code target}. */
    private static boolean reaches(String from, String target, Map<String, List<String>> edges,
                                   List<String> path, Set<String> seen) {
        if (!seen.add(from)) {
            return false;
        }
        path.add(from);
        for (String next : edges.getOrDefault(from, List.of())) {
            if (next.equals(target) || reaches(next, target, edges, path, seen)) {
                return true;
            }
        }
        path.remove(path.size() - 1);
        return false;
    }

    /**
     * A {@code depends on} names a behavior whose requirement set is not empty (spec
     * {@code [#depends-on]}): one with no implementation of its own, or one whose {@code let} declares
     * {@code depends on} in turn, here or in a module this one imports.
     *
     * <p>Reported where the clause is written, and the three ways it can be wrong are told apart
     * because the fix differs: a behavior that depends on nothing is called instead, a {@code >->}
     * composition cannot be rested on because its requirements are not written, and a name that is no
     * behavior has to be declared or imported. The body check would see only a call it cannot type
     * and report all three as an arbitrary JVM call (E1401, issue #96).
     */
    static void checkRequiresAreInjectionTargets(Ast.Module module, Map<String, ReqSig> reqSigs,
                                                 Map<String, ReqSig> calleeSigs) {
        for (Ast.BehaviorDef b : module.behaviors()) {
            if (!(b instanceof Ast.SpecBehavior spec)) {
                continue;
            }
            for (Ast.Var required : spec.dependsOn()) {
                if (required.unresolved() || reqSigs.containsKey(required.bare())) {
                    continue;
                }
                String req = required.bare();
                // Three ways a name can be wrong here, told apart because the fix differs. A
                // behavior that depends on nothing has nothing to inject and is called instead; a
                // composition cannot be rested on because its requirements are not written; a name
                // that is no behavior has to be declared or imported. Which of the three is read off
                // what the name was resolved to, so an imported composition is the composition case
                // rather than the unknown one — scanning this module's own behaviors would only find
                // the local ones. All are reported at the name, as the clause that names nothing is.
                String key = calleeSigs.containsKey(req) ? "e1607.nothing"
                        : required.denotes() instanceof ValueName.Behavior ? "e1607.composition"
                        : "e1607.unknown";
                throw CompileException.of(
                        Diagnostic.of("E1607", key).title("e1607.title")
                                .at(required.pos(), required.name().length())
                                .args(spec.name(), req)
                                .hint(key + ".hint", spec.name(), req)
                                .build(),
                        "`behavior " + spec.name() + "` declares `depends on " + req + "`, which"
                                + " depends on nothing of its own to inject (spec [#depends-on])");
            }
        }
    }

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
            Map<String, Sig> sigs, Symbols symbols) {
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
            Sig sig = sigs.get(pipe.name());
            if (sig == null) {
                // A composition with no signature is one that rests on a stage naming nothing,
                // reported where that stage was written. There is no output to hold a declaration
                // against, and the other compositions still have theirs.
                continue;
            }
            Set<TypeName> inferred = TypeOps.leafCases(sig.out(), symbols);
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
            Set<TypeName> declaredCases = TypeOps.leafCases(TypeOps.successType(declared, symbols), symbols);
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
     * {@code depends on} (12.6); the trailing ones name the injection targets in declared order and
     * do not bind values — they resolve as inline calls to those behaviors.
     */
    static Core checkSpecFn(Ast.SpecBehavior spec, Ast.FnDef fn, Ast.Expr inlinedBody,
                                    InvariantChecker.Source discharge,
                                    Symbols symbols, Map<String, ReqSig> calleeSigs,
                                    Map<String, ReqSig> reqSigs, HelperInliner inliner,
                                    Map<String, Type> recursiveHelperFns,
                                    Map<String, DataChecker.Constructs> recHelperConstructs,
                                    List<Diagnostic> warnings) {
        if (fn.declaredReturn() != null) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.impl.noreturn").title("check.impl.title")
                            .at(fn.pos()).args(fn.name(), spec.name()).build(),
                    "`let " + fn.name() + "` implements `behavior " + spec.name()
                            + "`, so its return type comes from the behavior — do not declare one"
                            + " (spec 13.1)");
        }
        for (Ast.Var required : spec.dependsOn()) {
            // A `depends on` naming nothing was reported where it is written. What this fn's trailing
            // parameters should be called comes from those names, so there is nothing to hold them
            // against — saying they are named wrongly would name the spelling that denotes nothing.
            if (required.unresolved()) {
                throw new Unanswerable(required.pos());
            }
        }
        int nBusiness = spec.params().size();
        int nReq = spec.dependsOn().size();
        if (fn.params().size() != nBusiness + nReq) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.impl.arity").title("check.impl.title")
                            .at(fn.pos()).args(fn.name(), fn.params().size(), spec.name(), nBusiness, nReq)
                            .build(),
                    "`let " + fn.name() + "` takes " + fn.params().size()
                            + " parameter(s) but `behavior " + spec.name() + "` has " + nBusiness
                            + " input(s)" + (nReq == 0 ? "" : " plus " + nReq + " injected")
                            + " (spec 13.1)");
        }
        for (Ast.FnParam p : fn.params()) {
            // a pattern in parameter position names a type, but it is not an annotation: it opens
            // the input the behavior already typed
            if (p.type() != null && !p.typeFromPattern()) {
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
            String want = spec.dependsOn().get(i).bare();
            if (!got.equals(want)) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.impl.reqorder").title("check.impl.title")
                                .at(fn.pos()).args(fn.name(), got, want).build(),
                        "`let " + fn.name() + "` parameter `" + got + "` should be `" + want
                                + "`: what `depends on` names becomes the trailing parameters in declared order"
                                + " (spec 12.6)");
            }
        }

        Scope env = Scope.NONE;
        for (Ast.FnParam p : fn.params()) {
            Elaborator.rejectBuiltinShadow(p.name(), p.pos());
        }
        Elaborator.rejectBuiltinShadowing(fn.written());
        for (int i = 0; i < nBusiness; i++) {
            env = env.with(fn.params().get(i).binder(),
                    TypeOps.successType(spec.params().get(i).type(), symbols));
        }
        Type output = TypeOps.successType(spec.ret(), symbols);
        // recursive helpers this behavior calls resolve through their signatures (spec 13.1); merged
        // only for typing, so the construction and dependency walks below still see the business params alone.
        // A parameter of the same name wins: a binding in force wins over the declaration it shadows
        // (spec §fn-rules), so an input written `depth` is the input and not the helper spelled that way.
        Scope tenv = env.reaching(recursiveHelperFns);
        // Check functions passed to helper parameters (e.g. a combinator's predicate) against their
        // declared types first, so a mismatch names the parameter, not the derivation it expands to.
        // A nested fold reaches `List.foldFrom` inside a block, so its signature must be in scope here.
        HelperTyping.checkFunctionArgs(fn.written(), tenv, symbols, reqSigs, inliner);
        // The body arrives with helper calls already expanded (the Lower stage, ADR-0021): it is
        // checked as one expression, so a helper's constructions and injected calls count toward this
        // behavior's permission and dependencies — exactly as if the code had been written inline (12.5).
        Ast.Expr body = inlinedBody;

        // push the declared output type into the body so a body that is directly an empty collection
        // (or a construction whose field is one) takes the declared type rather than a bottom
        Core elaboratedBody = Elaborator.elaborate(body, tenv,
                new CheckContext(symbols, null, reqSigs).withCallees(calleeSigs), output);
        Type rt = elaboratedBody.type();
        if (!TypeOps.assignable(rt, output, symbols)) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.behavior.return").title("check.type.mismatch.title")
                            .at(body.pos()).args(spec.name(), Type.show(output), Type.show(rt))
                            .diff(Type.show(rt, output), Type.show(output, rt)).build(),
                    "behavior `" + spec.name() + "` returns " + output + " but its `let` body is " + rt);
        }

        // One expression (spec 16.4): this single walk sees every construction, including under a
        // desugared `guard`.
        DataChecker.Constructs constructed = DataChecker.Constructs.empty();
        DataChecker.collectConstructs(body, constructed, symbols, recHelperConstructs);
        // `constructs` on an fn-backed behavior is optional: its construction permission is internal
        // (invisible to callers, unlike `depends on`), so with the body visible the set can be inferred
        // (ADR-0002). Omit it and inference stands. Declare it and it must match the body exactly —
        // under-declaration is E1002, over-declaration E1006 — so an explicit clause stays a checkable,
        // readable record of what is newly built versus passed through (spec 12.3), the same exact
        // match `depends on` gets (E1602/E1603). Injected behaviors still declare it: no body to infer
        // from, and it drives factory generation (spec 13.3).
        if (!spec.constructs().isEmpty()) {
            // Both sides name types, and a type has one identity however it is written — `up.Amount`
            // and an `Amount` an import brings in are the same one. Each side keeps its own spelling
            // in whatever it has to report.
            Set<TypeName> declared = new HashSet<>(MatchElaborator.denoted(spec.constructs()));
            for (Map.Entry<TypeName, String> built : constructed.originated().entrySet()) {
                if (!declared.contains(built.getKey())) {
                    String c = built.getValue();
                    throw CompileException.of(
                            Diagnostic.of("E1002", "e1002.msg").at(spec.pos())
                                    .args(spec.name(), c).hint("e1002.hint").build(),
                            "Behavior `" + spec.name() + "` constructs `" + c
                                    + "` but does not declare `constructs " + c + "`.");
                }
            }
            for (Ast.Name declaredName : spec.constructs()) {
                String name = declaredName.written();
                if (!constructed.builds(declaredName.denotes())) {
                    throw CompileException.of(
                            Diagnostic.of("E1006", "e1006.msg").at(spec.pos())
                                    .args(spec.name(), name).hint("e1006.hint").build(),
                            "Behavior `" + spec.name() + "` declares `constructs " + name
                                    + "` but never builds " + name + " — it passes an existing"
                                    + " value through. Remove it from the `constructs` clause.");
                }
            }
        }
        // The `depends on` clause must match what the fn actually calls (spec 12.6): missing -> E1602,
        // extra -> E1603.
        List<String> actual = requiredCalls(body, reqSigs.keySet());
        List<String> declared = new ArrayList<>();
        for (Ast.Var required : spec.dependsOn()) {
            declared.add(required.bare());
        }
        for (String call : actual) {
            if (!declared.contains(call)) {
                throw CompileException.of(
                        Diagnostic.of("E1602", "e1602.msg").at(spec.pos())
                                .args(fn.name(), call, spec.name()).hint("e1602.hint").build(),
                        "`let " + fn.name() + "` calls `" + call + "`, which has no implementation, but"
                                + " `behavior " + spec.name() + "` does not declare `depends on " + call + "`.");
            }
        }
        for (String req : declared) {
            if (!actual.contains(req)) {
                throw CompileException.of(
                        Diagnostic.of("E1603", "e1603.msg").at(spec.pos())
                                .args(spec.name(), req, fn.name()).hint("e1603.hint").build(),
                        "`behavior " + spec.name() + "` declares `depends on " + req + "`, but `let "
                                + fn.name() + "` never calls it. Remove it from the `depends on` clause.");
            }
        }
        // Intraprocedural invariant discharge: seed from the input
        // newtypes' invariants, refine along each `guard`/`if` guard, and check every construction.
        // A guard-discharged one is silent; an unproven one is a warning (a possible abort); one the
        // guards prove must fail on a reachable path is an error (the path-sensitive generalization of
        // the constant `金額(-5)` check).
        // the invariant analysis reads its own atoms off the spellings a body writes, so it is
        // handed the name view rather than the bindings
        InvariantChecker.Findings inv = InvariantChecker.analyze(discharge, env.byName(), symbols);
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
                        .map(SpecChecker::termName)
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
    static void rejectTupleIO(Ast.SpecBehavior spec, Symbols symbols) {
        for (Ast.Param p : spec.params()) {
            for (Ast.TypeTerm c : p.type().cases()) {
                if (carriesTuple(c, symbols)) {
                    throw CompileException.of(
                            Diagnostic.of(null, "check.param.tuple").title("check.boundary.title")
                                    .at(p.pos(), p.name().length()).args(p.name()).build(),
                            "parameter `" + p.name() + "` is a tuple; a tuple has no external"
                                    + " representation and cannot cross the boundary, so a behavior's"
                                    + " input must be a named data (ADR-0036)");
                }
            }
        }
        for (Ast.TypeTerm c : spec.ret().cases()) {
            if (carriesTuple(c, symbols)) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.output.tuple").title("check.boundary.title")
                                .at(spec.pos()).args(spec.name()).build(),
                        "behavior `" + spec.name() + "` outputs a tuple; a tuple cannot cross the"
                                + " boundary, so a behavior's output must be a named data or a sum of"
                                + " them (ADR-0036)");
            }
        }
    }

    /**
     * Every effective member of a behavior's output goes by a name of its own. A member is named by
     * a {@code match} arm and by the {@code "type"} discriminator of the external representation, and
     * both take the name as written, so two types that are written the same cannot be members of one
     * union. Asked after a named sum is expanded to its leaves, since a sum contributes its cases.
     *
     * <p>Asked of the signature rather than of what was written, so a composition is subject to it as
     * well: two stages may depart cases of one spelling from two modules.
     */
    static void checkUnionMemberNames(Ast.Module module, Map<String, Sig> sigs, Symbols symbols) {
        for (Ast.BehaviorDef b : module.behaviors()) {
            Sig sig = sigs.get(b.name());
            if (sig == null) {
                continue;
            }
            TypeName[] clash = TypeOps.ambiguousMembers(sig.out(), symbols);
            if (clash == null) {
                continue;
            }
            throw CompileException.of(
                    Diagnostic.of(null, "check.union.samename").title("check.boundary.title")
                            .at(b.pos()).args(clash[1].name(), clash[0].module(), clash[1].module())
                            .hint("check.union.samename.hint").build(),
                    "the output of `" + b.name() + "` has two members written `" + clash[1].name()
                            + "`: the one `" + clash[0].module() + "` declares and the one `"
                            + clash[1].module() + "` declares");
        }
    }

    /**
     * A member of an output union lays its fields flatly beside the `"type"` discriminator the union
     * writes (spec 19.8), so a member declaring a field of that name and the tag want one key. The
     * same rule a sum's cases are under, asked of the signature so a composition is subject to it too.
     */
    static void checkUnionMemberFields(Ast.Module module, Map<String, Sig> sigs, Symbols symbols) {
        for (Ast.BehaviorDef b : module.behaviors()) {
            Sig sig = sigs.get(b.name());
            if (sig == null || !(sig.out() instanceof Type.Union)) {
                continue;
            }
            TypeName carrying = TypeOps.memberCarryingField(sig.out(), DISCRIMINATOR, symbols);
            if (carrying == null) {
                continue;
            }
            throw CompileException.of(
                    Diagnostic.of(null, "check.member.discriminatorfield").title("check.boundary.title")
                            .at(b.pos()).args(carrying.name(), DISCRIMINATOR, b.name())
                            .hint("check.case.discriminatorfield.hint", DISCRIMINATOR).build(),
                    "`" + carrying.name() + "` is a member of the output of `" + b.name() + "` and"
                            + " declares a field `" + DISCRIMINATOR + "`, which is the discriminator"
                            + " that union writes beside the fields; rename the field");
        }
    }

    /** The key a derived codec writes the case name under (spec 11.2). */
    private static final String DISCRIMINATOR = "type";

    /**
     * A behavior's input is decoded and its output encoded, so neither may carry a function — at any
     * depth, since a function hides as easily inside a {@code List} or a {@code Map} as it stands on
     * its own. Asked of the type rather than of the syntax: what the position requires is an external
     * representation, and a function has none (ADR-0004).
     */
    static void rejectFunctionIO(Ast.SpecBehavior spec, Symbols symbols) {
        for (Ast.Param p : spec.params()) {
            Type t = TypeOps.successType(p.type(), symbols);
            if (!TypeOps.hasExternalForm(t, symbols)) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.param.function").title("check.boundary.title")
                                .at(p.pos(), p.name().length()).args(p.name(), Type.show(t)).build(),
                        "parameter `" + p.name() + "` carries a function (" + Type.show(t)
                                + "); a function has no external representation, so it cannot cross"
                                + " the boundary into a behavior");
            }
        }
        Type out = TypeOps.successType(spec.ret(), symbols);
        if (!TypeOps.hasExternalForm(out, symbols)) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.output.function").title("check.boundary.title")
                            .at(spec.pos()).args(spec.name(), Type.show(out)).build(),
                    "behavior `" + spec.name() + "` outputs a function (" + Type.show(out)
                            + "); a function has no external representation, so it cannot cross the"
                            + " boundary out of a behavior");
        }
    }

    /**
     * A behavior does not answer an optional (ADR-0011). "Might not be there" as a business result is
     * the model's own sum — {@code -> 会員 | 会員なし} — which reads closer to the specification than
     * {@code Option<会員>}, and it is what a reader of the answer gets to match on. It also keeps the
     * runtime's {@code Option} out of the Java-facing signature an exposed behavior generates
     * (ADR-0008).
     *
     * <p>Asked of the resolved type, so it holds whichever way the type was written: naming it and
     * marking it with {@code ?} reach the same type, and a rule attached to one spelling is a rule the
     * other spelling walks past (issue #202). A data with an optional field is unaffected — that is a
     * field, which is where an optional belongs.
     */
    static void rejectOptionalOutput(Ast.SpecBehavior spec, Symbols symbols) {
        if (!(TypeOps.successType(spec.ret(), symbols) instanceof Type.OptionOf opt)) {
            return;
        }
        String element = Type.show(opt.element());
        throw CompileException.of(
                Diagnostic.of(null, "check.output.optional").title("check.boundary.title")
                        .at(spec.pos()).args(spec.name(), Type.show(opt))
                        .hint("check.output.optional.hint", element).build(),
                "behavior `" + spec.name() + "` outputs an optional (" + Type.show(opt)
                        + "); an absence a behavior answers with is a case of the model's own sum —"
                        + " write `-> " + element + " | <the absence>` and name what it is (ADR-0011)");
    }

    /** A behavior's input and output cross a decoder/encoder, so a map they carry is a JSON object
     * and its keys are strings (ADR-0040). A map that stays inside the body is unrestricted — the
     * same rule, read where it applies. */
    static void rejectNonBoundaryMapKeyIO(Ast.SpecBehavior spec, Symbols symbols) {
        for (Ast.Param p : spec.params()) {
            Type bad = TypeOps.nonBoundaryMapKey(TypeOps.successType(p.type(), symbols), symbols);
            if (bad != null) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.map.key.param").title("check.boundary.title")
                                .at(p.pos(), p.name().length()).args(p.name(), Type.show(bad))
                                .hint("check.map.key.param.hint").build(),
                        "parameter `" + p.name() + "` carries a Map keyed by " + Type.show(bad)
                                + "; a Map crossing the boundary must be keyed by String, a"
                                + " String-backed newtype (`data X = String`), Date or DateTime"
                                + " (ADR-0040)");
            }
        }
        Type bad = TypeOps.nonBoundaryMapKey(TypeOps.successType(spec.ret(), symbols), symbols);
        if (bad != null) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.map.key.output").title("check.boundary.title")
                            .at(spec.pos()).args(spec.name(), Type.show(bad))
                            .hint("check.map.key.output.hint").build(),
                    "behavior `" + spec.name() + "` outputs a Map keyed by " + Type.show(bad)
                            + "; a Map crossing the boundary must be keyed by String, a String-backed"
                            + " newtype (`data X = String`), Date or DateTime (ADR-0040)");
        }
    }

    /** Whether a tuple is what stops {@code term} crossing the boundary. Asked of the type the term
     * stands for, so the walk and the rule live where every other capability question does; a term
     * that names no type answers no, and the function check below reports it. */
    private static boolean carriesTuple(Ast.TypeTerm term, Symbols symbols) {
        return TypeOps.withoutExternalForm(TypeOps.resolveTerm(term, symbols), symbols)
                instanceof Type.TupleOf;
    }

    /** How a written term reads in a diagnostic that quotes the source. */
    private static String termName(Ast.TypeTerm term) {
        return term instanceof Ast.TypeRef ref ? ref.name() : "a function";
    }

    static void checkInjectionConstructs(Ast.SpecBehavior spec, Symbols symbols,
                                                 boolean exposeAll, Set<String> exposed) {
        for (Ast.Name name : spec.constructs()) {
            String c = name.written();
            TypeName built = name.denotes();
            if (symbols.get(built) instanceof Ast.UnitData) {
                continue;   // a unit has a generated factory
            }
            // What Java needs is a way in: the decoder, which a module publishes by exposing the type.
            // For a type of another module that is its own `exposing` to answer, not this one's.
            // `exposed` lists this module's own names, so the resolved name is what to look up — a
            // type of this module written through it (`down.Out`) is the same one as `Out`
            boolean buildable = symbols.isForeign(built)
                    ? symbols.isExposed(built) : exposeAll || exposed.contains(built.name());
            if (!buildable) {
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
     * What a module reaches out with may not rest on what it keeps to itself.
     *
     * <p>Two things reach out. A name in {@code exposing} is one: a reader names it, so it names the
     * types its fields and its signature are written in, and a type this module keeps to itself has
     * no name there and a class the reader may not touch. The abstract base of an injected behavior
     * is the other, whether or not the behavior is exposed, because it is public whatever
     * {@code exposing} says (spec 13.3) and the implementation writes the input and output types
     * where it overrides {@code apply} — with no raw-typed override to fall back on, since the
     * erased signature clashes with the one being overridden rather than overriding it.
     *
     * <p>Reported here, where the module decides it, rather than at each reader that runs into it —
     * as Rust's {@code private_interfaces} and F#'s {@code FS0410} do.
     *
     * <p>This does not reach the <em>cases</em> of a sum, or of an output written as more than one
     * case. Those are generated as a union interface which is public regardless, and a case reaches
     * a reader through the decoder or through the {@code protected} factory rather than by being
     * named — which is what E1305's unit-data allowance rests on.
     */
    static void checkExposedSurface(Ast.Module module, Set<String> injectionTargets,
                                    Map<String, Sig> sigs, Symbols symbols,
                                    boolean exposeAll, Set<String> exposed,
                                    Map<String, Type> definitionTypes) {
        if (exposeAll) {
            return;   // nothing is kept to the module, so nothing can be rested on
        }
        for (Ast.Def d : module.defs()) {
            if (!(d instanceof Ast.Data data) || !exposed.contains(data.name())) {
                continue;
            }
            // Read through the includes: a spread flattens another data's fields into this one, so
            // they are this data's fields on the generated class and carry their types with them.
            for (Map.Entry<String, Type> f : TypeOps.fieldTypes(data, symbols).entrySet()) {
                refuseHidden(f.getValue(), "check.surface.field", data.name(), f.getKey(),
                        "check.surface.hint", data.pos(), symbols, exposeAll, exposed);
            }
        }
        // A published definition may not rest on a type the module keeps to itself: a reader would
        // hold a value it has no name for, or be unable to write the argument it has to pass. Both
        // questions are asked of the definition's *type* — what it stands for, and what it takes —
        // and never of the constructions its body happens to make on the way, which are its own
        // workings and would put every inner type back in the reader's import list.
        //
        // The types are settled from the body (ADR-0066), so they are read from what the standalone
        // helper check settled rather than from the shape of the body: a definition may name a type
        // it does not build (`let published (n: Int) : List<Hidden> = []`), and reading the body for
        // constructions answers about a different thing and misses that one.
        //
        // A behavior's input and output are asked below, under its own name; a behavior's own `let`
        // is an implementation and not one of the module's definitions.
        for (Ast.FnDef fn : HelperInliner.helpersOf(module).values()) {
            if (!(fn.body() instanceof Ast.FnBody.Written) || !exposed.contains(fn.name())) {
                continue;
            }
            for (Ast.FnParam p : fn.params()) {
                refuseHidden(TypeOps.resolveParamType(p.type(), symbols), "check.surface.param",
                        fn.name(), p.name(), "check.surface.hint", fn.pos(), symbols, exposeAll,
                        exposed);
            }
            // A definition whose check did not settle a type has none to ask about: it failed its own
            // check, which is reported, or it returns a function, which does not cross into another
            // module as a value (ADR-0004).
            Type stands = definitionTypes.get(fn.name());
            if (stands != null) {
                refuseHidden(stands, "check.surface.value", fn.name(), null, "check.surface.hint",
                        fn.pos(), symbols, exposeAll, exposed);
            }
        }
        // Read off the signature map rather than the declarations: a composition's input and output
        // are inferred from its stages, so they are written nowhere, and this is the one place both
        // kinds of behavior answer the same question.
        for (Ast.BehaviorDef b : module.behaviors()) {
            boolean injected = injectionTargets.contains(b.name());
            Sig sig = sigs.get(b.name());
            if (sig == null || (!injected && !exposed.contains(b.name()))) {
                continue;
            }
            String inKey = injected ? "check.inject.hiddeninput" : "check.surface.input";
            String outKey = injected ? "check.inject.hiddenoutput" : "check.surface.output";
            String hint = injected ? "check.inject.hidden.hint" : "check.surface.hint";
            for (Type in : sig.ins()) {
                refuseHidden(in, inKey, b.name(), null, hint, b.pos(), symbols, exposeAll, exposed);
            }
            refuseHidden(sig.out(), outKey, b.name(), null, hint, b.pos(),
                    symbols, exposeAll, exposed);
        }
    }

    private static void refuseHidden(Type written, String key, String owner, String field,
                                     String hint, SourcePos pos, Symbols symbols,
                                     boolean exposeAll, Set<String> exposed) {
        if (written == null) {
            return;   // an unresolved reference has its own error
        }
        // `mentions` stops at the first match, so the predicate keeps the name it stopped on: a
        // collection carries its element out with it too (`List<Id>` names `Id`).
        TypeName[] hidden = new TypeName[1];
        Type.mentions(written, t -> {
            if (t instanceof Type.Ref ref && !nameableOutside(ref.name(), symbols, exposeAll, exposed)) {
                hidden[0] = ref.name();
                return true;
            }
            return false;
        });
        if (hidden[0] == null) {
            return;
        }
        String name = hidden[0].name();
        Diagnostic.Builder d = Diagnostic.of(null, key).title("check.module.title").at(pos);
        d = field == null ? d.args(owner, name) : d.args(owner, field, name);
        throw CompileException.of(d.hint(hint, name, owner).build(),
                "`" + owner + "` reaches outside this module and rests on `" + name
                        + "`, which is not in `exposing`");
    }

    /** Whether a reader outside the declaring module can write {@code name}. */
    private static boolean nameableOutside(TypeName name, Symbols symbols, boolean exposeAll,
                                           Set<String> exposed) {
        return symbols.isForeign(name)
                ? symbols.isExposed(name) : exposeAll || exposed.contains(name.name());
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
        Map<String, List<Ast.Var>> pipeStages = PipelineSigs.pipelineStages(module);
        for (Ast.BehaviorDef b : module.behaviors()) {
            if (!(b instanceof Ast.PipeBehavior pipe)) {
                continue;
            }
            // check the flattened stages: a named intermediate splices in its own first stage, which
            // then sits after `>->` and so must be single-input too (spec 14.1, 14.2)
            List<Ast.Var> stages = PipelineSigs.flattenStages(pipe.stages(), pipeStages,
                    pipe.pos());
            for (int i = 1; i < stages.size(); i++) {
                String stage = stages.get(i).bare();
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
        if (e instanceof Ast.Apply call && requiredNames.contains(call.reaches())
                && !out.contains(call.reaches())) {
            out.add(call.written());
        }
        // Every subexpression, through the one exhaustive walk — a call to an injected behavior may
        // sit anywhere. Listing the node kinds here instead left `-dep(x)` and `(dep(x), y)` out of
        // the set, and a block's requirements still float out to the behavior that passes it
        // (spec 12.5, 29) because a Block's body is one of its children.
        Ast.forEachChild(e, c -> collectRequiredCalls(c, requiredNames, out));
    }

}
