package souther.compiler.check;

import souther.compiler.ast.Hir;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.msg.DeclarationMessage;
import souther.compiler.diag.msg.BehaviorMessage;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Behavior signatures and pipeline composition: what each behavior takes and yields, and how
 * {@code >->} routes a stage's output cases into the next stage (spec §composition).
 *
 * <p>The routing walk here is the one the backend replays when it emits a pipeline, so
 * {@link #stageOut} and {@link #mainlineCases} are public: the two must agree on which cases a
 * stage consumes and which retire.
 */
public final class PipelineSigs {

    private PipelineSigs() {}

    /** Builds the input/output signature of every behavior, checking pipeline composition. */
    public static Map<String, Sig> signatures(Hir.Module module, Symbols symbols) {
        return signatures(module, symbols, Map.of());
    }

    /**
     * Builds the input/output signature of every behavior, checking pipeline composition. The
     * {@code imported} map seeds the resolvable behaviors with those imported from other modules
     * (spec §modules, §composition), so a stage naming an imported behavior resolves through {@link #stageSig}.
     */
    public static Map<String, Sig> signatures(Hir.Module module, Symbols symbols,
                                              Map<String, Sig> imported) {
        Map<String, Sig> sigs = new HashMap<>(imported);
        for (Hir.BehaviorDef b : module.behaviors()) {
            if (b instanceof Hir.SpecBehavior spec) {
                // A behavior's signature is what it declares, whether a `let` implements it here or the Java
                // side is injected (spec §injected-behavior): both are named the same way from a `>->` or a
                // `depends on`, and both need the output union's generated interface. Where the arity rules
                // out a use — every stage after the first takes one input (§sequential-composition) — the
                // composition says so; leaving the name out of this map instead reports it as one that was
                // never declared. What the declaration says is admitted here, in the making of the signature,
                // and there is no other way to make one. A behavior resting on a name that denotes nothing
                // has no signature to build and is left out: the name was reported where it was written.
                try {
                    sigs.put(spec.name(), SignatureBoundary.of(spec, symbols));
                } catch (Unanswerable _) {
                    // deliberately empty: see above
                }
            }
        }
        Map<String, List<Hir.Var>> pipeStages = pipelineStages(module);
        for (Hir.BehaviorDef b : module.behaviors()) {
            if (b instanceof Hir.PipeBehavior pipe) {
                try {
                    sigs.put(pipe.name(), pipeSig(pipe, sigs, symbols, pipeStages));
                } catch (Unanswerable _) {
                    // A stage that names nothing was reported where it was written, and this
                    // composition has no signature to work out. It is one behavior: the others keep
                    // theirs, and the module is checked past it. Nothing will be emitted — the name
                    // that denotes nothing is what `Names.Sound` answers for.
                }
            }
        }
        return sigs;
    }

    /** Maps each pipeline behavior's name to its declared stages (for flattening, spec §type-routing). */
    public static Map<String, List<Hir.Var>> pipelineStages(Hir.Module module) {
        Map<String, List<Hir.Var>> stages = new HashMap<>();
        for (Hir.BehaviorDef b : module.behaviors()) {
            if (b instanceof Hir.PipeBehavior pipe) {
                stages.put(pipe.name(), pipe.stages());
            }
        }
        return stages;
    }

    /**
     * Flattens a pipeline's stage list, splicing any stage that is itself a pipeline into its own
     * (recursively flattened) stages (spec §type-routing). This is what makes {@code >->} associative:
     * {@code half >-> finish} with {@code half = split >-> work} routes over {@code split, work,
     * finish}, exactly as the flat form would, so a retired case stays retired across a named
     * intermediate. A pipeline viewed on its own still has the merged output its own stages produce.
     */
    public static List<Hir.Var> flattenStages(List<Hir.Var> stages,
                                                   Map<String, List<Hir.Var>> pipeStages,
                                                   SourcePos pos) {
        List<Hir.Var> out = new ArrayList<>();
        flattenInto(stages, pipeStages, out, new LinkedHashSet<>(), pos);
        return out;
    }

    private static void flattenInto(List<Hir.Var> stages,
                                    Map<String, List<Hir.Var>> pipeStages,
                                    List<Hir.Var> out, Set<String> inProgress, SourcePos pos) {
        for (Hir.Var s : stages) {
            // A stage that names nothing was reported where it is written. It is no pipeline to
            // splice in, and the composition it is part of is abandoned where its signature is
            // asked for rather than here.
            List<Hir.Var> sub = s.unresolved() ? null : pipeStages.get(s.bare());
            if (sub == null) {
                out.add(s);
                continue;
            }
            if (!inProgress.add(s.bare())) {
                throw CompileException.of(Diagnostic
                                .at(pos).say(new BehaviorMessage.APipelineComposesWithItself(s.name())).build());
            }
            flattenInto(sub, pipeStages, out, inProgress, pos);
            inProgress.remove(s.bare());
        }
    }

    /**
     * The signature of a pipeline stage.
     *
     * <p>Which behavior a stage names was answered when the module's names were resolved, so there
     * is no spelling to test here. A stage that names nothing was reported there, and this
     * composition has no meaning to work out: the behavior it belongs to is abandoned, and the
     * definitions around it are checked as they would be without it.
     */
    public static Sig stageSig(Hir.Var stage, Map<String, Sig> sigs, Symbols symbols,
                               SourcePos pos) {
        if (stage.unresolved()) {
            throw new Unanswerable(stage.pos());
        }
        Sig s = sigs.get(stage.bare());
        if (s == null) {
            // The behavior is declared by a module this compilation could not work out — reported
            // on that module, whose author is the one who can act on it.
            throw new Unanswerable(stage.pos());
        }
        return s;
    }

    private static Sig pipeSig(Hir.PipeBehavior pipe, Map<String, Sig> sigs, Symbols symbols,
                               Map<String, List<Hir.Var>> pipeStages) {
        // flatten nested pipeline stages so `>->` is associative (spec §type-routing)
        List<Hir.Var> stages = flattenStages(pipe.stages(), pipeStages, pipe.pos());
        Sig first = stageSig(stages.get(0), sigs, symbols, pipe.pos());
        Type mainline = first.outputType();
        Set<TypeName> retired = new LinkedHashSet<>();
        for (int i = 1; i < stages.size(); i++) {
            Sig g = stageSig(stages.get(i), sigs, symbols, pipe.pos());
            // Every stage after the first takes exactly one input (spec §sequential-composition).
            // `checkStagesAreSingleInput` says so too and is the diagnostic the author usually sees, but
            // signatures are built before it runs and are also built for an imported module that was never
            // checked here — so the arity is confirmed rather than assumed, or `route` would index an empty
            // input list.
            if (g.ins().size() != 1) {
                throw CompileException.of(Diagnostic
                                .at(pipe.pos()).say(new BehaviorMessage.AStageAfterTheFirstTakesOneInput(stages.get(i).name(), String.valueOf(g.ins().size()), pipe.name())).build());
            }
            mainline = route(mainline, g, retired, symbols, pipe.pos());
        }
        Type out = withRetired(mainline, retired);
        // an optional declared output must match the inferred one exactly (spec
        // §declared-composition-output): neither a missing case (too narrow) nor an extra one (too wide) is
        // accepted.
        if (pipe.declaredOut() != null) {
            Set<TypeName> inferred = TypeOps.leafCases(out, symbols);
            Set<TypeName> declared = TypeOps.leafCases(TypeOps.successType(pipe.declaredOut()), symbols);
            if (!inferred.equals(declared)) {
                throw CompileException.of(Diagnostic.at(pipe.pos())
                                
                                .hint(new DeclarationMessage.UpdateTheOutputOrHandleTheCase())
                                .say(new DeclarationMessage.TheDeclaredOutputIsNotWhatThePipelineProduces(pipe.name(), caseList(declared), caseList(inferred))).build());
            }
        }
        // The pipeline takes whatever its first stage takes (spec §sequential-composition), which arrived admitted with
        // that stage's own signature and is not asked again. What it answers is a type nobody wrote
        // — the last stage's answer, merged with the cases that left the main line — so that is
        // where the boundary is asked, once, about a composition.
        return new Sig(first.ins(),
                SignatureBoundary.composedOutput(pipe.name(), pipe.pos(), out, symbols));
    }

    /** Formats a set of case names as {@code A | B} (sorted, for a stable diagnostic). */
    static String caseList(Set<TypeName> cases) {
        java.util.TreeSet<String> names = new java.util.TreeSet<>();
        for (TypeName c : cases) {
            names.add(c.name());
        }
        return String.join(" | ", names);
    }

    /** The pipeline's output: what the last stage yields, plus everything that left the main line. */
    private static Type withRetired(Type mainline, Set<TypeName> retired) {
        if (retired.isEmpty()) {
            return mainline;
        }
        Set<TypeName> all = new LinkedHashSet<>(TypeOps.caseNamesOf(mainline));
        if (all.isEmpty()) {
            throw new IllegalStateException("cannot merge non-data stage output with retired cases");
        }
        all.addAll(retired);
        return TypeOps.caseSetType(all);
    }

    /** The main-line leaf cases {@code g} accepts — the ones the backend routes into it (spec §type-routing). */
    public static List<TypeName> mainlineCases(Type mainline, Sig g, Symbols symbols) {
        List<TypeName> accepted = new ArrayList<>();
        for (TypeName caseName : TypeOps.leafCases(mainline, symbols)) {
            if (TypeOps.assignable(Type.ref(caseName), g.in(), symbols)) {
                accepted.add(caseName);
            }
        }
        return accepted;
    }

    /** The main line after {@code g} runs, for the backend's routing walk. */
    public static Type stageOut(Type mainline, Sig g, Symbols symbols, SourcePos pos) {
        return route(mainline, g, new LinkedHashSet<>(), symbols, pos);
    }

    /**
     * One step of type-routed composition (spec §type-routing). Returns the new main line — what {@code g}
     * yields — and adds the cases {@code g} did not accept to {@code retired}.
     *
     * <p>A case that leaves the main line does not come back: later stages are only offered the
     * main line. That is what makes this Railway (§type-routing). Feeding the retired cases onward instead
     * would let a stage pick up something an earlier stage had already dropped, which changes the
     * meaning of a pipeline depending on where it is split.
     *
     * <p>Naming an intermediate does not lose the split (spec §type-routing): a pipeline stage is flattened
     * into its own stages before routing ({@link #flattenStages}), so `fg >-> h` with
     * `fg = f >-> g` routes over `f, g, h` — a retired case stays retired, exactly as in the flat
     * `f >-> g >-> h`. That flattening is what makes `>->` associative; a value never carries a mark
     * saying it once left a main line (§unmarked-sum), the plumbing is structural. Viewed on its own, `fg`
     * still has the merged sum `f`+`g` produce as its output.
     */
    private static Type route(Type mainline, Sig g, Set<TypeName> retired, Symbols symbols,
                              SourcePos pos) {
        Type in = g.in();
        if (TypeOps.isDataLike(mainline)) {
            Set<TypeName> consumed = new LinkedHashSet<>();
            Set<TypeName> passed = new LinkedHashSet<>();
            // route over the leaf cases: a named sum output splits into its members, so a stage that
            // accepts one of them consumes it while the rest retire (spec §sum-data, §type-routing)
            for (TypeName caseName : TypeOps.leafCases(mainline, symbols)) {
                if (TypeOps.assignable(Type.ref(caseName), in, symbols)) {
                    consumed.add(caseName);
                } else {
                    passed.add(caseName);
                }
            }
            if (consumed.isEmpty()) {
                throw CompileException.of(Diagnostic
                                .at(pos)
                                .diff(Type.show(mainline, in), Type.show(in, mainline))
                                .hint(new DeclarationMessage.MakeTheLeftOutputACaseTheRightAccepts())
                                .say(new DeclarationMessage.TheseBehaviorsCannotBeComposed()).build());
            }
            retired.addAll(passed);
            return g.outputType();
        }
        if (!mainline.equals(in)) {
            throw CompileException.of(Diagnostic
                            .at(pos)
                            .diff(Type.show(mainline, in), Type.show(in, mainline))
                            .hint(new DeclarationMessage.MakeTheLeftOutputACaseTheRightAccepts())
                            .say(new DeclarationMessage.TheseBehaviorsCannotBeComposed()).build());
        }
        return g.outputType();
    }
}
