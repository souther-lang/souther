package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.core.Core;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.DeclarationMessage;
import souther.compiler.diag.msg.DataMessage;
import souther.compiler.diag.msg.BehaviorMessage;
import souther.compiler.diag.msg.TypeMessage;
import souther.compiler.diag.msg.InjectionMessage;
import souther.compiler.diag.msg.ModuleMessage;
import souther.compiler.diag.DiagnosticRenderer;
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
    static void checkBehaviorsDoNotRecurse(Hir.Module module) {
        Set<String> names = new LinkedHashSet<>();
        for (Hir.BehaviorDef b : module.behaviors()) {
            names.add(b.name());
        }
        Map<String, List<String>> edges = new LinkedHashMap<>();
        Map<String, Hir.FnDef> fns = new LinkedHashMap<>();
        for (Hir.FnDef fn : module.fns()) {
            fns.put(fn.name(), fn);
        }
        for (Hir.BehaviorDef b : module.behaviors()) {
            List<String> out = new ArrayList<>();
            switch (b) {
                case Hir.SpecBehavior spec -> {
                    for (Hir.Var req : spec.dependsOn()) {
                        if (req.unresolved()) {
                            continue;   // it names no behavior, so it is no edge of this graph
                        }
                        if (names.contains(req.bare()) && !out.contains(req.bare())) {
                            out.add(req.bare());
                        }
                    }
                    Hir.FnDef fn = fns.get(spec.name());
                    if (fn != null) {
                        for (String called : requiredCalls(fn.writtenBody(), names)) {
                            if (!out.contains(called)) {
                                out.add(called);
                            }
                        }
                    }
                }
                case Hir.PipeBehavior pipe -> {
                    for (Hir.Var stage : pipe.stages()) {
                        if (stage.unresolved()) {
                            continue;   // it names no behavior, so it is no edge of this graph
                        }
                        if (names.contains(stage.bare()) && !out.contains(stage.bare())) {
                            out.add(stage.bare());
                        }
                    }
                }
            }
            edges.put(b.name(), out);
        }
        for (Hir.BehaviorDef b : module.behaviors()) {
            List<String> path = new ArrayList<>();
            if (reaches(b.name(), b.name(), edges, path, new HashSet<>())) {
                path.add(b.name());
                throw CompileException.of(Diagnostic
                                .at(b.pos())
                                .hint(new DeclarationMessage.ABehaviorDoesNotRecurse()).say(new DeclarationMessage.ABehaviorReachesItself(b.name(), String.join(" -> ", path))).build());
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
     * and report all three as a name that resolves to nothing (E1023).
     */
    static void checkRequiresAreInjectionTargets(Hir.Module module, Map<String, ReqSig> reqSigs,
                                                 Map<String, ReqSig> calleeSigs) {
        for (Hir.BehaviorDef b : module.behaviors()) {
            if (!(b instanceof Hir.SpecBehavior spec)) {
                continue;
            }
            for (Hir.Var required : spec.dependsOn()) {
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
                boolean dependsOnNothing = calleeSigs.containsKey(req);
                boolean aComposition = required.denotes() instanceof ValueName.Behavior;
                throw CompileException.of(Diagnostic.at(required.written().reportedAt())
                        .say(dependsOnNothing
                                ? new DeclarationMessage
                                        .DependsOnNamesSomethingThatDependsOnNothing(spec.name(),
                                                req)
                                : aComposition
                                        ? new DeclarationMessage.DependsOnNamesAComposition(
                                                spec.name(), req)
                                        : new DeclarationMessage.DependsOnNamesNoSuchBehavior(
                                                spec.name(), req))
                        .hint(dependsOnNothing
                                ? new DeclarationMessage.RemoveItAndCallItDirectly(req)
                                : aComposition
                                        ? new DeclarationMessage
                                                .ACompositionsRequirementsAreNotWritten(req)
                                        : new DeclarationMessage.DeclareItHereOrImportIt(req))
                        .build());
            }
        }
    }

    /**
     * An exposed composition ({@code >->}) behavior must declare its output in the {@code exposing} list
     * ({@code exposing ( name : A | B )}, spec §declared-composition-output, ADR-0024), and the declaration
     * must match the inferred output exactly. A far-away change that grows the output then fails here, at the
     * module boundary, instead of reaching separately-compiled consumers unannounced.
     *
     * <p>The requirement applies only to a composition that is explicitly exposed: a module with no
     * {@code exposing} publishes everything with inference intact, and a non-composition behavior
     * states its type at its definition, so a signature on one is rejected.
     */
    static void checkExposedPipeOutputs(Hir.Module module, Set<String> exposed,
            Map<String, Sig> sigs, Symbols symbols) {
        Set<String> pipeNames = new HashSet<>();
        for (Hir.BehaviorDef b : module.behaviors()) {
            if (b instanceof Hir.PipeBehavior p) {
                pipeNames.add(p.name());
            }
        }
        // a signature in `exposing` is only meaningful on a composition behavior
        for (String name : module.exposedOutputs().keySet()) {
            if (!pipeNames.contains(name)) {
                throw CompileException.of(Diagnostic.at(module.pos()).say(new DeclarationMessage.OnlyACompositionTakesAnOutputSignature(name)).build());
            }
        }
        // every exposed composition must declare its output, matching the inferred one
        for (Hir.BehaviorDef b : module.behaviors()) {
            if (!(b instanceof Hir.PipeBehavior pipe) || !exposed.contains(pipe.name())) {
                continue;
            }
            Sig sig = sigs.get(pipe.name());
            if (sig == null) {
                // A composition with no signature is one that rests on a stage naming nothing,
                // reported where that stage was written. There is no output to hold a declaration
                // against, and the other compositions still have theirs.
                continue;
            }
            Set<TypeName> inferred = TypeOps.leafCases(sig.outputType(), symbols);
            Hir.RetType declared = module.exposedOutputs().get(pipe.name());
            if (declared == null) {
                throw CompileException.of(Diagnostic.at(pipe.pos())
                                
                                .hint(new DeclarationMessage.WriteTheOutputSignature(pipe.name(), PipelineSigs.caseList(inferred)))
                                .say(new DeclarationMessage.AnExposedCompositionDeclaresItsOutput(pipe.name())).build());
            }
            Set<TypeName> declaredCases = TypeOps.leafCases(TypeOps.successType(declared), symbols);
            if (!inferred.equals(declaredCases)) {
                throw CompileException.of(Diagnostic.at(pipe.pos())
                                
                                .hint(new DeclarationMessage.UpdateTheOutputOrHandleTheCase())
                                .say(new DeclarationMessage.TheDeclaredOutputIsNotWhatThePipelineProduces(pipe.name(), PipelineSigs.caseList(declaredCases), PipelineSigs.caseList(inferred))).build());
            }
        }
    }

    /**
     * Checks a behavior's {@code fn} implementation against the behavior's declared signature
     * (spec §fn-declaration). The {@code fn}'s parameters are the behavior's inputs followed by its
     * {@code depends on} (§depends-on); the trailing ones name the injection targets in declared order and
     * do not bind values — they resolve as inline calls to those behaviors.
     */
    static Core checkSpecFn(Hir.SpecBehavior spec, Hir.FnDef fn, Hir.Expr inlinedBody,
                                    InvariantChecker.Source discharge,
                                    Symbols symbols, Map<String, ReqSig> calleeSigs,
                                    Map<String, ReqSig> reqSigs, HelperInliner inliner,
                                    Map<String, Type> recursiveHelperFns,
                                    Map<String, DataChecker.Constructs> recHelperConstructs,
                                    List<Diagnostic> warnings) {
        if (fn.declaredReturn() != null) {
            throw CompileException.of(Diagnostic
                            .at(fn.pos()).say(new BehaviorMessage.AnImplementationsReturnComesFromTheBehavior(fn.name(), spec.name())).build());
        }
        for (Hir.Var required : spec.dependsOn()) {
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
            throw CompileException.of(Diagnostic
                            .at(fn.pos())
                            .say(new BehaviorMessage.TheImplementationTakesAnotherNumberOfParameters(fn.name(), String.valueOf(fn.params().size()), spec.name(), String.valueOf(nBusiness), String.valueOf(nReq))).build());
        }
        for (Hir.FnParam p : fn.params()) {
            // a pattern in parameter position names a type, but it is not an annotation: it opens
            // the input the behavior already typed
            if (p.type() != null && !p.typeFromPattern()) {
                throw CompileException.of(Diagnostic
                                .at(p.pos()).say(new BehaviorMessage.AnImplementationsParametersTakeTheirTypesFromIt(fn.name(), spec.name(), p.name())).build());
            }
        }
        for (int i = 0; i < nReq; i++) {
            String got = fn.params().get(nBusiness + i).name();
            String want = spec.dependsOn().get(i).bare();
            if (!got.equals(want)) {
                throw CompileException.of(Diagnostic
                                .at(fn.pos()).say(new BehaviorMessage.AnInjectedParameterIsOutOfOrder(fn.name(), got, want)).build());
            }
        }

        Scope env = Scope.NONE;
        for (Hir.FnParam p : fn.params()) {
            Elaborator.rejectBuiltinShadow(p.name(), p.pos());
        }
        Elaborator.rejectBuiltinShadowing(fn.writtenBody());
        for (int i = 0; i < nBusiness; i++) {
            env = env.with(fn.params().get(i).binder(),
                    TypeOps.successType(spec.params().get(i).type()));
        }
        Type output = TypeOps.successType(spec.ret());
        // recursive helpers this behavior calls resolve through their signatures (spec §fn-declaration); merged
        // only for typing, so the construction and dependency walks below still see the business params alone.
        // A parameter of the same name wins: a binding in force wins over the declaration it shadows
        // (spec §fn-rules), so an input written `depth` is the input and not the helper spelled that way.
        Scope tenv = env.reaching(recursiveHelperFns);
        // Check functions passed to helper parameters (e.g. a combinator's predicate) against their
        // declared types first, so a mismatch names the parameter, not the derivation it expands to.
        // A nested fold reaches `List.foldFrom` inside a block, so its signature must be in scope here.
        HelperTyping.checkFunctionArgs(fn.writtenBody(), tenv, symbols, reqSigs, inliner);
        // The body arrives with helper calls already expanded (the Lower stage, ADR-0021): it is
        // checked as one expression, so a helper's constructions and injected calls count toward this
        // behavior's permission and dependencies — exactly as if the code had been written inline (§blocks).
        Hir.Expr body = inlinedBody;

        // push the declared output type into the body so a body that is directly an empty collection
        // (or a construction whose field is one) takes the declared type rather than a bottom
        Core elaboratedBody = Elaborator.elaborate(body, tenv,
                new CheckContext(symbols, null, reqSigs).withCallees(calleeSigs), output);
        Type rt = elaboratedBody.type();
        if (!TypeOps.assignable(rt, output, symbols)) {
            throw CompileException.of(Diagnostic
                            .at(body.pos())
                            .diff(Type.show(rt, output), Type.show(output, rt)).say(new BehaviorMessage.TheBodyIsNotWhatTheBehaviorReturns(spec.name(), Type.show(output), Type.show(rt))).build());
        }

        // One expression (spec §guard): this single walk sees every construction, including under a
        // desugared `guard`.
        DataChecker.Constructs constructed = DataChecker.Constructs.empty();
        DataChecker.collectConstructs(body, constructed, symbols, recHelperConstructs);
        // `constructs` on an fn-backed behavior is optional: its construction permission is internal
        // (invisible to callers, unlike `depends on`), so with the body visible the set can be inferred
        // (ADR-0002). Omit it and inference stands. Declare it and it must match the body exactly —
        // under-declaration is E1002, over-declaration E1006 — so an explicit clause stays a checkable,
        // readable record of what is newly built versus passed through (spec §constructs), the same exact
        // match `depends on` gets (E1602/E1603). Injected behaviors still declare it: no body to infer
        // from, and it drives factory generation (spec §java-base-class).
        if (!spec.constructs().isEmpty()) {
            // Both sides name types, and a type has one identity however it is written — `up.Amount`
            // and an `Amount` an import brings in are the same one. Each side keeps its own spelling
            // in whatever it has to report.
            Set<TypeName> declared = new HashSet<>(MatchElaborator.denoted(spec.constructs()));
            // Every way this clause and this body disagree, and not the first of them. Both sides
            // are worked out once and whole before any of it is said, so stopping at one left the
            // author to fix that one, compile, and be told the next — a walk down the call graph,
            // one build per name. One clause is one thing to rewrite, and a clause that is short of
            // one name and carrying another it does not build is wrong in both directions at once:
            // reporting the two separately is two builds to learn what one reading of the body
            // already knows.
            //
            // One violation is one diagnostic. Each names the type it is about and carries the hint
            // for that type, so an editor has one thing to act on per name rather than a sentence
            // listing several. What is short comes before what is extra, in the order the body
            // builds them (`originated` keeps the order it collected them in) and then the order the
            // clause writes them — every one of them is at the declaration, so nothing reorders them
            // afterwards.
            List<Diagnostic> disagreements = new ArrayList<>();
            for (Map.Entry<TypeName, String> built : constructed.originated().entrySet()) {
                if (!declared.contains(built.getKey())) {
                    String c = built.getValue();
                    disagreements.add(Diagnostic.at(spec.pos())
                                    .hint(new DeclarationMessage.AddTheConstructsEntry(spec.name(), c)).say(new DeclarationMessage.ItConstructsWithoutDeclaringIt(spec.name(), c)).build());
                }
            }
            for (Hir.Name declaredName : spec.constructs()) {
                String name = declaredName.written();
                if (!constructed.builds(declaredName.denotes())) {
                    disagreements.add(Diagnostic.at(spec.pos())
                                    .hint(new DeclarationMessage.RemoveTheConstructsEntry(name)).say(new DeclarationMessage.ItDeclaresConstructsAndNeverBuilds(spec.name(), name)).build());
                }
            }
            if (!disagreements.isEmpty()) {
                throw CompileException.ofAll(disagreements,
                        DiagnosticRenderer.legacyBody(disagreements.get(0)));
            }
        }
        // The `depends on` clause must match what the fn actually calls (spec §depends-on): missing -> E1602,
        // extra -> E1603.
        List<String> actual = requiredCalls(body, reqSigs.keySet());
        List<String> declared = new ArrayList<>();
        for (Hir.Var required : spec.dependsOn()) {
            declared.add(required.bare());
        }
        for (String call : actual) {
            if (!declared.contains(call)) {
                throw CompileException.of(Diagnostic.at(spec.pos())
                                .hint(new DeclarationMessage.AddTheDependsOnEntry(call, spec.name())).say(new DeclarationMessage.ItCallsSomethingWithNoImplementation(fn.name(), call, spec.name())).build());
            }
        }
        for (String req : declared) {
            if (!actual.contains(req)) {
                throw CompileException.of(Diagnostic.at(spec.pos())
                                .hint(new DeclarationMessage.RemoveTheDependsOnEntry(req)).say(new DeclarationMessage.ItDeclaresDependsOnAndNeverCallsIt(spec.name(), req, fn.name())).build());
            }
        }
        // Intraprocedural invariant discharge: seed from the input
        // newtypes' invariants, refine along each `guard`/`if` guard, and check every construction.
        // A guard-discharged one is silent; an unproven one is a warning (a possible abort); one the
        // guards prove must fail on a reachable path is an error (the path-sensitive generalization of
        // the constant `金額(-5)` check).
        // The discharge representation is typed by the checker like any other, keeping the language's
        // own operations standing because that is what the analysis reading it has rules about. A
        // representation there is none of is not analyzed at all, rather than analyzed over the
        // emitted tree, whose operations are no longer operations.
        Core dischargeBody = discharge == null ? null
                : Elaborator.elaborate(discharge.body(), tenv,
                        new CheckContext(symbols, null, reqSigs).withCallees(calleeSigs)
                                .forDischarge(), output);
        InvariantChecker.Findings inv = InvariantChecker.analyze(dischargeBody,
                discharge == null ? Map.of() : discharge.invariants(), env, symbols);
        warnings.addAll(inv.warnings());
        if (!inv.errors().isEmpty()) {
            throw inv.errors().get(0);
        }
        return elaboratedBody;
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
    static void checkUnionMemberNames(Hir.Module module, Map<String, Sig> sigs, Symbols symbols) {
        for (Hir.BehaviorDef b : module.behaviors()) {
            Sig sig = sigs.get(b.name());
            if (sig == null) {
                continue;
            }
            TypeName[] clash = TypeOps.ambiguousMembers(sig.outputType(), symbols);
            if (clash == null) {
                continue;
            }
            throw CompileException.of(Diagnostic
                            .at(b.pos())
                            .hint(new TypeMessage.AMemberIsNamedByItsWrittenName()).say(new TypeMessage.OneNameForTwoMembers(clash[1].name(), clash[0].module(), clash[1].module())).build());
        }
    }

    /**
     * A member of an output union lays its fields flatly beside the `"type"` discriminator the union
     * writes (spec §jvm-anonymous-union), so a member declaring a field of that name and the tag want one key. The
     * same rule a sum's cases are under, asked of the signature so a composition is subject to it too.
     */
    static void checkUnionMemberFields(Hir.Module module, Map<String, Sig> sigs, Symbols symbols) {
        for (Hir.BehaviorDef b : module.behaviors()) {
            Sig sig = sigs.get(b.name());
            if (sig == null || !(sig.outputType() instanceof Type.Union)) {
                continue;
            }
            TypeName carrying = TypeOps.memberCarryingField(sig.outputType(), DISCRIMINATOR, symbols);
            if (carrying == null) {
                continue;
            }
            throw CompileException.of(Diagnostic
                            .at(b.pos())
                            .hint(new DataMessage.TheTagAndTheFieldWantOneKey(DISCRIMINATOR)).say(new DataMessage.AMemberDeclaresTheDiscriminatorField(carrying.name(), DISCRIMINATOR, b.name())).build());
        }
    }

    /** The key a derived codec writes the case name under (spec §encoder-derivation). */
    private static final String DISCRIMINATOR = "type";


    /**
     * An injected behavior's declared {@code constructs} must each be Java-buildable (spec §java-base-class):
     * a unit data (the base class hands the implementation a {@code protected} factory) or an
     * exposed data (its {@code decoder} is public). A non-unit, unexposed one is E1305 — Java has
     * no way to mint it.
     */
    static void checkInjectionConstructs(Hir.SpecBehavior spec, Symbols symbols,
                                                 boolean exposeAll, Set<String> exposed) {
        for (Hir.Name name : spec.constructs()) {
            String c = name.written();
            TypeName built = name.denotes();
            if (symbols.declarations().declaration(built) instanceof Hir.UnitData) {
                continue;   // a unit has a generated factory
            }
            // What Java needs is a way in: the decoder, which a module publishes by exposing the type.
            // For a type of another module that is its own `exposing` to answer, not this one's.
            // `exposed` lists this module's own names, so the resolved name is what to look up — a
            // type of this module written through it (`down.Out`) is the same one as `Out`
            boolean buildable = symbols.scope().isForeign(built)
                    ? symbols.scope().isExposed(built) : exposeAll || exposed.contains(built.name());
            if (!buildable) {
                throw CompileException.of(Diagnostic.at(spec.pos())
                                .hint(new DeclarationMessage.ExposeItOrMakeItAUnitData(c)).say(new DeclarationMessage.AnInjectedBehaviorConstructsWhatIsKept(spec.name(), c)).build());
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
     * {@code exposing} says (spec §java-base-class) and the implementation writes the input and output types
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
    static void checkExposedSurface(Hir.Module module, Set<String> injectionTargets,
                                    Map<String, Sig> sigs, Symbols symbols,
                                    boolean exposeAll, Set<String> exposed,
                                    Map<String, Type> definitionTypes) {
        if (exposeAll) {
            return;   // nothing is kept to the module, so nothing can be rested on
        }
        for (Hir.Def d : module.defs()) {
            if (!(d instanceof Hir.Data data) || !exposed.contains(data.name())) {
                continue;
            }
            // Read through the includes: a spread flattens another data's fields into this one, so
            // they are this data's fields on the generated class and carry their types with them.
            for (Map.Entry<String, Type> f : TypeOps.fieldTypes(data, symbols).entrySet()) {
                refuseHidden(f.getValue(),
                        hidden -> Diagnostic.say(new ModuleMessage.AnExposedFieldRestsOnWhatIsKept(data.name(),
                                f.getKey(), hidden))
                                .hint(new ModuleMessage.WhatReachesOutMayNotRestOnWhatIsKept(hidden,
                                data.name())),
                        data.pos(), symbols, exposeAll, exposed);
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
        for (Hir.FnDef fn : HelperInliner.helpersOf(module).values()) {
            if (!(fn.body() instanceof Hir.FnBody.Written) || !exposed.contains(fn.name())) {
                continue;
            }
            for (Hir.FnParam p : fn.params()) {
                refuseHidden(TypeOps.resolveParamType(p.type()),
                        hidden -> Diagnostic
                                .say(new ModuleMessage.AnExposedArgumentRestsOnWhatIsKept(fn.name(),
                                        p.name(), hidden))
                                .hint(new ModuleMessage.WhatReachesOutMayNotRestOnWhatIsKept(hidden,
                                        fn.name())),
                        fn.pos(), symbols, exposeAll, exposed);
            }
            // A definition whose check did not settle a type has none to ask about: it failed its own
            // check, which is reported, or it returns a function, which does not cross into another
            // module as a value (ADR-0004).
            Type stands = definitionTypes.get(fn.name());
            if (stands != null) {
                refuseHidden(stands,
                        hidden -> Diagnostic.say(new ModuleMessage.AnExposedValueRestsOnWhatIsKept(fn.name(),
                                hidden))
                                .hint(new ModuleMessage.WhatReachesOutMayNotRestOnWhatIsKept(hidden,
                                fn.name())),
                        fn.pos(), symbols, exposeAll, exposed);
            }
        }
        // Read off the signature map rather than the declarations: a composition's input and output
        // are inferred from its stages, so they are written nowhere, and this is the one place both
        // kinds of behavior answer the same question.
        for (Hir.BehaviorDef b : module.behaviors()) {
            boolean injected = injectionTargets.contains(b.name());
            Sig sig = sigs.get(b.name());
            if (sig == null || (!injected && !exposed.contains(b.name()))) {
                continue;
            }
            // An injected behavior and an exposed one are refused for different reasons and told
            // different things to do, so each says its refusal and its repair together rather than
            // the two being chosen apart and paired up here.
            for (Type in : sig.inputTypes()) {
                refuseHidden(in,
                        hidden -> injected
                                ? Diagnostic
                                        .say(new InjectionMessage.AnInjectedInputRestsOnWhatIsKept(
                                                b.name(), hidden))
                                        .hint(new InjectionMessage
                                                .TheBaseClassIsPublicWhateverExposingSays(hidden))
                                : Diagnostic
                                        .say(new ModuleMessage.AnExposedInputRestsOnWhatIsKept(
                                                b.name(), hidden))
                                        .hint(new ModuleMessage
                                                .WhatReachesOutMayNotRestOnWhatIsKept(hidden,
                                                        b.name())),
                        b.pos(), symbols, exposeAll, exposed);
            }
            refuseHidden(sig.outputType(),
                    hidden -> injected
                            ? Diagnostic
                                    .say(new InjectionMessage.AnInjectedOutputRestsOnWhatIsKept(
                                            b.name(), hidden))
                                    .hint(new InjectionMessage
                                            .TheBaseClassIsPublicWhateverExposingSays(hidden))
                            : Diagnostic
                                    .say(new ModuleMessage.AnExposedOutputRestsOnWhatIsKept(
                                            b.name(), hidden))
                                    .hint(new ModuleMessage.WhatReachesOutMayNotRestOnWhatIsKept(
                                            hidden, b.name())),
                    b.pos(), symbols, exposeAll, exposed);
        }
    }

    private static void refuseHidden(Type written,
                                     java.util.function.Function<String, Diagnostic.Builder> saying,
                                     SourcePos pos, Symbols symbols,
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
        throw CompileException.of(saying.apply(name).at(pos).build());
    }

    /** Whether a reader outside the declaring module can write {@code name}. */
    private static boolean nameableOutside(TypeName name, Symbols symbols, boolean exposeAll,
                                           Set<String> exposed) {
        return symbols.scope().isForeign(name)
                ? symbols.scope().isExposed(name) : exposeAll || exposed.contains(name.name());
    }

    /**
     * Every stage after the first takes exactly one input (spec §sequential-composition): {@code >->} hands a single
     * value along.
     *
     * <p>The first stage is not restricted — it consumes the pipeline's own arguments, and the
     * pipeline simply takes what it takes. The spec DSL relies on this
     * (`behavior 却下して差し戻す = 却下する >-> 差し戻す`, where `却下する` reads
     * `事前承認待ち AND 却下者ID`); requiring the whole chain to be single-input would reject the
     * very line 14.1 cites.
     */
    static void checkStagesAreSingleInput(Hir.Module module) {
        Map<String, Integer> arity = new HashMap<>();
        for (Hir.BehaviorDef b : module.behaviors()) {
            if (b instanceof Hir.SpecBehavior spec) {
                arity.put(spec.name(), spec.params().size());
            }
        }
        Map<String, List<Hir.Var>> pipeStages = PipelineSigs.pipelineStages(module);
        for (Hir.BehaviorDef b : module.behaviors()) {
            if (!(b instanceof Hir.PipeBehavior pipe)) {
                continue;
            }
            // check the flattened stages: a named intermediate splices in its own first stage, which
            // then sits after `>->` and so must be single-input too (spec §sequential-composition, §type-routing)
            List<Hir.Var> stages = PipelineSigs.flattenStages(pipe.stages(), pipeStages,
                    pipe.pos());
            for (int i = 1; i < stages.size(); i++) {
                if (stages.get(i).unresolved()) {
                    continue;   // reported where it is written; it declares no arity to hold it to
                }
                String stage = stages.get(i).bare();
                Integer n = arity.get(stage);
                if (n != null && n != 1) {
                    throw CompileException.of(Diagnostic
                                    .at(pipe.pos()).say(new BehaviorMessage.AStageAfterTheFirstTakesOneInput(stage, String.valueOf(n), pipe.name())).build());
                }
            }
        }
    }

    /** The distinct injection targets a fn body calls, in first-seen order. Calls may appear
     * anywhere in an expression (e.g. inline in a record literal), not only bound to a let. */
    public static List<String> requiredCalls(Hir.Expr body, java.util.Set<String> requiredNames) {
        List<String> calls = new java.util.ArrayList<>();
        collectRequiredCalls(body, requiredNames, calls);
        return calls;
    }

    private static void collectRequiredCalls(Hir.Expr e, Set<String> requiredNames, List<String> out) {
        if (e instanceof Hir.Apply call && call.answered() != null
                && requiredNames.contains(call.reaches())
                && !out.contains(call.reaches())) {
            out.add(call.written());
        }
        // Every subexpression, through the one exhaustive walk — a call to an injected behavior may
        // sit anywhere. Listing the node kinds here instead left `-dep(x)` and `(dep(x), y)` out of
        // the set, and a block's requirements still float out to the behavior that passes it
        // (spec §blocks, §requirement-propagation) because a Block's body is one of its children.
        Hir.forEachChild(e, c -> collectRequiredCalls(c, requiredNames, out));
    }

}
