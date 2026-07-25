package souther.compiler.check;

import souther.compiler.ast.Ast;
import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.SourcePos;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Behavior signatures and pipeline composition: what each behavior takes and yields, and how
 * {@code >->} routes a stage's output cases into the next stage (spec 14).
 *
 * <p>The routing walk here is the one the backend replays when it emits a pipeline, so
 * {@link #stageOut} and {@link #mainlineCases} are public: the two must agree on which cases a
 * stage consumes and which retire.
 */
public final class PipelineSigs {

    private PipelineSigs() {}

    /** Builds the input/output signature of every behavior, checking pipeline composition. */
    public static Map<String, Sig> signatures(Ast.Module module, Map<String, Ast.Def> symbols) {
        return signatures(module, symbols, Map.of());
    }

    /**
     * Builds the input/output signature of every behavior, checking pipeline composition. The
     * {@code imported} map seeds the resolvable behaviors with those imported from other modules
     * (spec 4, 14), so a stage naming an imported behavior resolves through {@link #stageSig}.
     */
    public static Map<String, Sig> signatures(Ast.Module module, Map<String, Ast.Def> symbols,
                                              Map<String, Sig> imported) {
        Set<String> fnNames = new HashSet<>();
        for (Ast.FnDef fn : module.fns()) {
            fnNames.add(fn.name());
        }
        Map<String, Sig> sigs = new HashMap<>(imported);
        for (Ast.BehaviorDef b : module.behaviors()) {
            if (b instanceof Ast.SpecBehavior spec) {
                if (fnNames.contains(spec.name())) {
                    // implemented: any arity — a multi-input behavior can be a pipeline's first stage (14.1)
                    List<Type> ins = new ArrayList<>();
                    for (Ast.Param p : spec.params()) {
                        ins.add(TypeOps.successType(p.type(), symbols));
                    }
                    sigs.put(spec.name(), new Sig(ins, TypeOps.successType(spec.ret(), symbols)));
                } else if (spec.params().size() == 1) {
                    // injected: only a single-input one can be a stage; a zero-arg one cannot (14.1)
                    sigs.put(spec.name(), new Sig(TypeOps.successType(spec.params().get(0).type(), symbols),
                            TypeOps.successType(spec.ret(), symbols)));
                }
            }
        }
        Map<String, List<String>> pipeStages = pipelineStages(module);
        for (Ast.BehaviorDef b : module.behaviors()) {
            if (b instanceof Ast.PipeBehavior pipe) {
                sigs.put(pipe.name(), pipeSig(pipe, sigs, symbols, pipeStages));
            }
        }
        return sigs;
    }

    /** Maps each pipeline behavior's name to its declared stages (for flattening, spec 14.2). */
    public static Map<String, List<String>> pipelineStages(Ast.Module module) {
        Map<String, List<String>> stages = new HashMap<>();
        for (Ast.BehaviorDef b : module.behaviors()) {
            if (b instanceof Ast.PipeBehavior pipe) {
                stages.put(pipe.name(), pipe.stages());
            }
        }
        return stages;
    }

    /**
     * Flattens a pipeline's stage list, splicing any stage that is itself a pipeline into its own
     * (recursively flattened) stages (spec 14.2). This is what makes {@code >->} associative:
     * {@code half >-> finish} with {@code half = split >-> work} routes over {@code split, work,
     * finish}, exactly as the flat form would, so a retired case stays retired across a named
     * intermediate. A pipeline viewed on its own still has the merged output its own stages produce.
     */
    public static List<String> flattenStages(List<String> stages, Map<String, List<String>> pipeStages,
                                             SourcePos pos) {
        List<String> out = new ArrayList<>();
        flattenInto(stages, pipeStages, out, new LinkedHashSet<>(), pos);
        return out;
    }

    private static void flattenInto(List<String> stages, Map<String, List<String>> pipeStages,
                                    List<String> out, Set<String> inProgress, SourcePos pos) {
        for (String s : stages) {
            List<String> sub = pipeStages.get(s);
            if (sub == null) {
                out.add(s);
                continue;
            }
            if (!inProgress.add(s)) {
                throw CompileException.of(
                        Diagnostic.of(null, "check.pipe.selfcompose").title("check.pipe.title")
                                .at(pos).args(s).build(),
                        "pipeline `" + s + "` composes with itself (a cycle)");
            }
            flattenInto(sub, pipeStages, out, inProgress, pos);
            inProgress.remove(s);
        }
    }

    /** The signature of a pipeline stage. Only behaviors compose with {@code >->}; decode/encode
     * are boundary edges, not stages (spec 14.1). */
    public static Sig stageSig(String stage, Map<String, Sig> sigs, Map<String, Ast.Def> symbols,
                               SourcePos pos) {
        if (stage.endsWith(".decoder") || stage.endsWith(".encoder")) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.pipe.boundary").title("check.pipe.title").at(pos).build(),
                    "decode/encode are boundary edges, not pipeline stages; `>->` composes behaviors"
                            + " only (spec 14.1)");
        }
        Sig s = sigs.get(stage);
        if (s == null) {
            throw CompileException.of(
                    Diagnostic.of(null, "check.unknown.behavior.msg")
                            .title("check.unknown.title")
                            .at(pos, stage.length())
                            .args(stage)
                            .suggestion(Suggest.candidate(stage, sigs.keySet()))
                            .build(),
                    "unknown behavior `" + stage + "` in pipeline" + Suggest.hint(stage, sigs.keySet()));
        }
        return s;
    }

    private static Sig pipeSig(Ast.PipeBehavior pipe, Map<String, Sig> sigs, Map<String, Ast.Def> symbols,
                               Map<String, List<String>> pipeStages) {
        // flatten nested pipeline stages so `>->` is associative (spec 14.2)
        List<String> stages = flattenStages(pipe.stages(), pipeStages, pipe.pos());
        Sig first = stageSig(stages.get(0), sigs, symbols, pipe.pos());
        Type mainline = first.out();
        Set<String> retired = new LinkedHashSet<>();
        for (int i = 1; i < stages.size(); i++) {
            mainline = route(mainline, stageSig(stages.get(i), sigs, symbols, pipe.pos()),
                    retired, symbols, pipe.pos());
        }
        Type out = withRetired(mainline, retired);
        // an optional declared output must match the inferred one exactly (spec 14.5): neither a
        // missing case (too narrow) nor an extra one (too wide) is accepted.
        if (pipe.declaredOut() != null) {
            Set<String> inferred = TypeOps.leafCases(out, symbols);
            Set<String> declared = TypeOps.leafCases(TypeOps.successType(pipe.declaredOut(), symbols), symbols);
            if (!inferred.equals(declared)) {
                throw CompileException.of(
                        Diagnostic.of("E1604", "e1604.msg").at(pipe.pos())
                                .args(pipe.name(), caseList(declared), caseList(inferred))
                                .hint("e1604.hint")
                                .build(),
                        "behavior " + pipe.name() + " declares -> " + caseList(declared)
                                + ", but the pipeline produces " + caseList(inferred)
                                + ". Update the declared output or handle the case.");
            }
        }
        // the pipeline takes whatever its first stage takes (spec 14.1)
        return new Sig(first.ins(), out);
    }

    /** Formats a set of case names as {@code A | B} (sorted, for a stable diagnostic). */
    static String caseList(Set<String> cases) {
        return String.join(" | ", new java.util.TreeSet<>(cases));
    }

    /** The pipeline's output: what the last stage yields, plus everything that left the main line. */
    private static Type withRetired(Type mainline, Set<String> retired) {
        if (retired.isEmpty()) {
            return mainline;
        }
        Set<String> all = new LinkedHashSet<>(TypeOps.caseNamesOf(mainline));
        if (all.isEmpty()) {
            throw new IllegalStateException("cannot merge non-data stage output with retired cases");
        }
        all.addAll(retired);
        return TypeOps.caseSetType(all);
    }

    /** The main-line leaf cases {@code g} accepts — the ones the backend routes into it (spec 14.2). */
    public static List<String> mainlineCases(Type mainline, Sig g, Map<String, Ast.Def> symbols) {
        List<String> accepted = new ArrayList<>();
        for (String caseName : TypeOps.leafCases(mainline, symbols)) {
            if (TypeOps.assignable(Type.ref(caseName), g.in(), symbols)) {
                accepted.add(caseName);
            }
        }
        return accepted;
    }

    /** The main line after {@code g} runs, for the backend's routing walk. */
    public static Type stageOut(Type mainline, Sig g, Map<String, Ast.Def> symbols, SourcePos pos) {
        return route(mainline, g, new LinkedHashSet<>(), symbols, pos);
    }

    /**
     * One step of type-routed composition (spec 14.2). Returns the new main line — what {@code g}
     * yields — and adds the cases {@code g} did not accept to {@code retired}.
     *
     * <p>A case that leaves the main line does not come back: later stages are only offered the
     * main line. That is what makes this Railway (14.2). Feeding the retired cases onward instead
     * would let a stage pick up something an earlier stage had already dropped, which changes the
     * meaning of a pipeline depending on where it is split.
     *
     * <p>Naming an intermediate does not lose the split (spec 14.2): a pipeline stage is flattened
     * into its own stages before routing ({@link #flattenStages}), so `fg >-> h` with
     * `fg = f >-> g` routes over `f, g, h` — a retired case stays retired, exactly as in the flat
     * `f >-> g >-> h`. That flattening is what makes `>->` associative; a value never carries a mark
     * saying it once left a main line (2.6), the plumbing is structural. Viewed on its own, `fg`
     * still has the merged sum `f`+`g` produce as its output.
     */
    private static Type route(Type mainline, Sig g, Set<String> retired, Map<String, Ast.Def> symbols,
                              SourcePos pos) {
        Type in = g.in();
        if (TypeOps.isDataLike(mainline)) {
            Set<String> consumed = new LinkedHashSet<>();
            Set<String> passed = new LinkedHashSet<>();
            // route over the leaf cases: a named sum output splits into its members, so a stage that
            // accepts one of them consumes it while the rest retire (spec 8.3, 14.2)
            for (String caseName : TypeOps.leafCases(mainline, symbols)) {
                if (TypeOps.assignable(Type.ref(caseName), in, symbols)) {
                    consumed.add(caseName);
                } else {
                    passed.add(caseName);
                }
            }
            if (consumed.isEmpty()) {
                throw CompileException.of(
                        Diagnostic.of("E1701", "e1701.msg")
                                .at(pos)
                                .diff(Type.show(mainline), Type.show(in))
                                .hint("e1701.hint")
                                .build(),
                        "Cannot compose behaviors: no output case of the left behavior is accepted by "
                                + "the right behavior's input. Left output: " + mainline + ", right input: " + in);
            }
            retired.addAll(passed);
            return g.out();
        }
        if (!mainline.equals(in)) {
            throw CompileException.of(
                    Diagnostic.of("E1701", "e1701.msg")
                            .at(pos)
                            .diff(Type.show(mainline), Type.show(in))
                            .hint("e1701.hint")
                            .build(),
                    "Cannot compose behaviors. Left output: " + mainline + ", right input: " + in);
        }
        return g.out();
    }
}
