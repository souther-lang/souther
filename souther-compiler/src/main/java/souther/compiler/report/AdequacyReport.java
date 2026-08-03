package souther.compiler.report;

import souther.compiler.ExampleVerifier;
import souther.compiler.ast.Ast;
import souther.compiler.meta.ModuleMetadata;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.InputCaseEvidence;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.observe.OutputCaseEvidence;
import souther.compiler.observe.RowOutcome;
import souther.compiler.query.Adequacy;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;
import souther.compiler.types.TypeName;

import tools.jackson.databind.node.ArrayNode;
import tools.jackson.databind.node.ObjectNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * How well a model's {@code example}s cover it, as something a person reads and a build reads.
 *
 * <p>This is the first version, and it answers only what needs no analysis: which behaviors there are,
 * which of them still have no {@code let}, how many rows each carries, and how many of those rows are
 * waiting rather than judging. The measures that need the model taken apart — which output cases the
 * rows witness, which equivalence classes and boundaries they reach, which branches they run — arrive
 * on top of these same observations.
 *
 * <p>{@code schemaVersion} is here from the first version because a build that reads this is written
 * against a shape, and a shape that changes without saying so breaks it silently. So is
 * {@code status}: an evaluation that could not read everything must not be read as one that found
 * nothing, and the difference is not visible in the numbers.
 */
public record AdequacyReport(int schemaVersion, String compilerVersion, MeasurementStatus status,
                             List<ModuleReport> modules) {

    public static final int SCHEMA_VERSION = 1;

    public record ModuleReport(String module, MeasurementStatus status,
                               List<Incompleteness> incompleteness, List<BehaviorReport> behaviors) {
        public ModuleReport {
            incompleteness = List.copyOf(incompleteness);
            behaviors = List.copyOf(behaviors);
        }
    }

    /**
     * @param injected  whether the behavior still has no {@code let} to run
     * @param rows      how many {@code example} rows name it, across every source that writes one
     * @param pending   how many of those are recorded rather than evaluated
     * @param signature what those rows establish about the cases of its inputs and its output
     */
    public record BehaviorReport(String name, boolean injected, int rows, int pending,
                                 MeasurementStatus status,
                                 Adequacy.SignatureEvidence signature) {}

    /** Reads a finished compile. {@link Compilation#answerEverything()} must have been asked first;
     * otherwise there is nothing to read and every behavior looks unexampled. */
    public static AdequacyReport of(Compilation compilation) {
        List<ModuleReport> modules = new ArrayList<>();
        MeasurementStatus overall = MeasurementStatus.COMPLETE;
        for (String name : compilation.modules()) {
            Ast.Module module = compilation.module(name);
            if (module == null) {
                continue;   // a module that did not get far enough to have behaviors
            }
            ModuleReport report = moduleReport(compilation, name, module);
            modules.add(report);
            overall = overall.and(report.status());
        }
        return new AdequacyReport(SCHEMA_VERSION, ModuleMetadata.compilerVersion(), overall,
                List.copyOf(modules));
    }

    private static ModuleReport moduleReport(Compilation compilation, String name, Ast.Module module) {
        Map<String, List<RowOutcome>> byTarget = new LinkedHashMap<>();
        List<Incompleteness> incompleteness = new ArrayList<>();
        for (String sourceId : compilation.exampleSourcesOf(name)) {
            Output.Examples.Of observed =
                    compilation.db().ask(new Output.Examples(name, sourceId)).value();
            if (observed == null) {
                // The rows of this source were never evaluated, so nothing here can be counted as
                // covered or as missing. Which is a fact about the measurement, not about the model.
                incompleteness.add(Incompleteness.of(Incompleteness.Code.RUNTIME_ABSENT, sourceId));
                continue;
            }
            incompleteness.addAll(observed.incompleteness());
            for (RowOutcome row : observed.rows()) {
                byTarget.computeIfAbsent(row.target(), _ -> new ArrayList<>()).add(row);
            }
        }
        Map<String, Adequacy.SignatureEvidence> signatures =
                compilation.db().ask(new Adequacy.Witnesses(name)).value();
        List<BehaviorReport> behaviors = new ArrayList<>();
        for (Ast.BehaviorDef behavior : module.behaviors()) {
            List<RowOutcome> rows = byTarget.getOrDefault(behavior.name(), List.of());
            int pending = (int) rows.stream()
                    .filter(r -> r.disposition() == souther.compiler.observe.Disposition.PENDING)
                    .count();
            boolean unreadable = incompleteness.stream()
                    .anyMatch(i -> behavior.name().equals(i.subject()));
            Adequacy.SignatureEvidence signature =
                    signatures == null ? null : signatures.get(behavior.name());
            behaviors.add(new BehaviorReport(behavior.name(),
                    ExampleVerifier.isPending(module, behavior.name()), rows.size(), pending,
                    unreadable ? MeasurementStatus.PARTIAL : MeasurementStatus.COMPLETE, signature));
        }
        MeasurementStatus status = incompleteness.isEmpty()
                ? MeasurementStatus.COMPLETE : MeasurementStatus.PARTIAL;
        return new ModuleReport(name, status, incompleteness, behaviors);
    }

    /** This report with only the modules and behaviors the caller asked about. A name that matches
     * nothing leaves an empty report rather than the whole one. */
    public AdequacyReport only(String module, String behavior) {
        List<ModuleReport> kept = new ArrayList<>();
        for (ModuleReport m : modules) {
            if (module != null && !module.equals(m.module())) {
                continue;
            }
            List<BehaviorReport> behaviors = behavior == null ? m.behaviors()
                    : m.behaviors().stream().filter(b -> behavior.equals(b.name())).toList();
            kept.add(new ModuleReport(m.module(), m.status(), m.incompleteness(), behaviors));
        }
        return new AdequacyReport(schemaVersion, compilerVersion, status, List.copyOf(kept));
    }

    /** How many rows are recorded and waiting for a {@code let}, across everything reported. */
    public int pendingRows() {
        return modules.stream().flatMap(m -> m.behaviors().stream())
                .mapToInt(BehaviorReport::pending).sum();
    }

    // --- rendering --------------------------------------------------------------------------------

    public String human() {
        StringBuilder out = new StringBuilder();
        int implemented = 0;
        int injected = 0;
        for (ModuleReport module : modules) {
            out.append(String.format("%-56s status: %s%n", module.module(),
                    module.status().name().toLowerCase(java.util.Locale.ROOT)));
            for (BehaviorReport behavior : module.behaviors()) {
                if (behavior.injected()) {
                    injected++;
                } else {
                    implemented++;
                }
                out.append(String.format("  %-24s %-13s rows %-4d pending %d%n", behavior.name(),
                        behavior.injected() ? "injected" : "implemented",
                        behavior.rows(), behavior.pending()));
                signature(out, behavior);
            }
            for (Incompleteness gap : module.incompleteness()) {
                out.append(String.format("    · not measured: %s (%s)%n", gap.subject(),
                        gap.code().name().toLowerCase(java.util.Locale.ROOT)));
            }
        }
        int total = implemented + injected;
        out.append(String.format("%n%d %s: %d implemented, %d injected; %d %s waiting for a `let`.%n",
                total, total == 1 ? "behavior" : "behaviors", implemented, injected,
                pendingRows(), pendingRows() == 1 ? "row" : "rows"));
        return out.toString();
    }

    /**
     * What the rows established about one behavior's signature, and what they left.
     *
     * <p>An unspecified case and an unverified one are printed apart because they ask different things
     * of the author. The first says nobody has written down that the model owes this answer; the
     * second says somebody has, and nothing has confirmed the model gives it. For a behavior with no
     * body only the first can be answered at all, so the second is not printed against one.
     */
    private static void signature(StringBuilder out, BehaviorReport behavior) {
        Adequacy.SignatureEvidence signature = behavior.signature();
        if (signature == null || signature.status() == MeasurementStatus.UNAVAILABLE) {
            return;
        }
        OutputCaseEvidence output = signature.output();
        if (!output.declared().isEmpty()) {
            out.append(String.format("    signature   out specified %d/%d  observed %d/%d "
                            + " verified %d/%d%s%n",
                    output.specified().size(), output.declared().size(),
                    output.observed().size(), output.declared().size(),
                    output.verified().size(), output.declared().size(),
                    signature.status() == MeasurementStatus.PARTIAL ? "   (partial)" : ""));
            for (TypeName missing : output.unspecified()) {
                out.append(String.format("      · no row expects `%s`%n", missing.name()));
            }
            if (!behavior.injected()) {
                for (TypeName missing : output.unverified()) {
                    if (!output.unspecified().contains(missing)) {
                        out.append(String.format("      · no row confirms `%s`%n", missing.name()));
                    }
                }
            }
        }
        for (int i = 0; i < signature.inputs().size(); i++) {
            InputCaseEvidence input = signature.inputs().get(i);
            if (input.declared().isEmpty()) {
                continue;
            }
            out.append(String.format("                in #%d specified %d/%d%n", i + 1,
                    input.specified().size(), input.declared().size()));
            for (TypeName missing : input.unspecified()) {
                out.append(String.format("      · no row uses `%s`%n", missing.name()));
            }
        }
    }

    private static final JsonMapper JSON = JsonMapper.builder().build();

    public String json() {
        ObjectNode root = JSON.createObjectNode();
        root.put("schemaVersion", schemaVersion);
        root.put("compilerVersion", compilerVersion);
        root.put("status", status.name().toLowerCase(java.util.Locale.ROOT));
        ArrayNode modulesOut = root.putArray("modules");
        for (ModuleReport module : modules) {
            ObjectNode m = modulesOut.addObject();
            m.put("module", module.module());
            m.put("status", module.status().name().toLowerCase(java.util.Locale.ROOT));
            ArrayNode gaps = m.putArray("incompleteness");
            for (Incompleteness gap : module.incompleteness()) {
                ObjectNode g = gaps.addObject();
                g.put("code", gap.code().name().toLowerCase(java.util.Locale.ROOT));
                g.put("subject", gap.subject());
                gap.at().ifPresent(where -> {
                    ObjectNode at = g.putObject("at");
                    at.put("sourceId", where.sourceId());
                    at.put("line", where.pos().line());
                    at.put("column", where.pos().column());
                });
            }
            ArrayNode behaviors = m.putArray("behaviors");
            for (BehaviorReport behavior : module.behaviors()) {
                ObjectNode b = behaviors.addObject();
                b.put("name", behavior.name());
                b.put("implementation", behavior.injected() ? "injected" : "implemented");
                b.put("rows", behavior.rows());
                b.put("pending", behavior.pending());
                b.put("status", behavior.status().name().toLowerCase(java.util.Locale.ROOT));
                signature(b, behavior.signature());
            }
        }
        return root.toPrettyString();
    }

    private static void signature(ObjectNode behavior, Adequacy.SignatureEvidence signature) {
        if (signature == null) {
            return;
        }
        ObjectNode out = behavior.putObject("signature");
        out.put("status", signature.status().name().toLowerCase(java.util.Locale.ROOT));
        ObjectNode output = out.putObject("output");
        names(output.putArray("declared"), signature.output().declared());
        names(output.putArray("specified"), signature.output().specified());
        names(output.putArray("observed"), signature.output().observed());
        names(output.putArray("verified"), signature.output().verified());
        output.put("unclassifiedRows", signature.output().unclassifiedRows());
        ArrayNode inputs = out.putArray("inputs");
        for (InputCaseEvidence input : signature.inputs()) {
            ObjectNode in = inputs.addObject();
            names(in.putArray("declared"), input.declared());
            names(in.putArray("specified"), input.specified());
            names(in.putArray("executed"), input.executed());
            names(in.putArray("verified"), input.verified());
            in.put("unclassifiedRows", input.unclassifiedRows());
        }
    }

    /** Case names, sorted: a report that changes order between runs cannot be compared between runs,
     * and the sets these come from keep the order the rows happened to arrive in. */
    private static void names(ArrayNode into, java.util.Set<TypeName> cases) {
        cases.stream().map(TypeName::name).sorted().forEach(into::add);
    }
}
