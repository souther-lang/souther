package souther.compiler.report;

import souther.compiler.ExampleVerifier;
import souther.compiler.ast.Ast;
import souther.compiler.meta.ModuleMetadata;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.InputCaseEvidence;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.observe.OutputCaseEvidence;
import souther.compiler.observe.RowOutcome;
import souther.compiler.partition.Partitions;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BoundaryAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.Output;
import souther.compiler.query.PartitionEvidence;
import souther.compiler.types.TypeName;

import tools.jackson.databind.node.ArrayNode;
import tools.jackson.databind.node.ObjectNode;
import tools.jackson.databind.json.JsonMapper;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

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
 *
 * <p>{@code askedLevel} is what the measures were asked for, and it is here because the evidence
 * cannot be read without it. A measure nobody asked for and a measure that could not be made both
 * come back {@code UNAVAILABLE}; only what was asked tells the two apart, and {@link #adequacy()}
 * answers differently for each. It is an input carried through rather than a value derived from the
 * modules, so filtering the report leaves it alone.
 */
public record AdequacyReport(int schemaVersion, String compilerVersion, Adequacy.Level askedLevel,
                             MeasurementStatus status, List<ModuleReport> modules) {

    public static final int SCHEMA_VERSION = 1;

    /**
     * Whether the rows meet what the asked measures require of them.
     *
     * <p>Apart from {@code status}, which says whether the measurement could be made at all. A
     * measurement that came back complete over a model with an arm nothing reaches is a measurement
     * that worked and a model that does not satisfy it, and one word cannot say both.
     */
    public enum AdequacyStatus {
        /** Every asked measure came to an answer, and none of them found a gap. */
        SATISFIED,
        /** Some asked measure found a gap. One is enough, whatever else could not be measured. */
        NOT_SATISFIED,
        /** No measure that could find a gap was asked, or one was asked and could not be made. */
        UNDETERMINED
    }

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
     * @param findings  what the measures found and nothing filled, which is what the lines under this
     *                  behavior print and what a build is warned about — one list, read three ways
     */
    public record BehaviorReport(String name, boolean injected, int rows, int pending,
                                 MeasurementStatus status,
                                 Adequacy.SignatureEvidence signature,
                                 PartitionEvidence partition,
                                 Adequacy.BranchEvidence branch,
                                 List<Adequacy.Finding> findings) {
        public BehaviorReport {
            findings = List.copyOf(findings);
        }

        /** The findings of one kind, in the order the measure produced them. */
        public List<Adequacy.Finding> of(Adequacy.Kind kind) {
            return findings.stream().filter(f -> f.kind() == kind).toList();
        }
    }

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
        Adequacy.Asked asked = compilation.db().ask(new Adequacy.Requested()).value();
        return new AdequacyReport(SCHEMA_VERSION, ModuleMetadata.compilerVersion(),
                asked == null ? Adequacy.Level.OFF : asked.level(), overall, List.copyOf(modules));
    }

    /**
     * What a behavior's own measures make of it.
     *
     * <p>A measure that came back partial is a measure that could not be made, and the status above it
     * has to say so — a report opening with `complete` over a line reading `undecided` is the one
     * confusion this field exists to prevent. `UNAVAILABLE` is not a degradation: a measure nobody
     * asked for, or one a behavior has nothing to answer, is not a measure that failed.
     */
    private static MeasurementStatus statusOf(Adequacy.SignatureEvidence signature,
                                              PartitionEvidence partition,
                                              Adequacy.BranchEvidence branch) {
        boolean partial = signature != null && signature.status() == MeasurementStatus.PARTIAL;
        partial |= branch != null && branch.status() == MeasurementStatus.PARTIAL;
        if (partition != null) {
            partial |= partition.axes().stream()
                    .anyMatch(a -> a.status() == MeasurementStatus.PARTIAL);
            partial |= partition.boundaries().stream()
                    .anyMatch(b -> b.status() == MeasurementStatus.PARTIAL);
            partial |= partition.pairs().status() == MeasurementStatus.PARTIAL;
            // What was dropped for being past a limit is measurement that did not happen either.
            partial |= !partition.omitted().isEmpty() || partition.pairs().truncated();
        }
        return partial ? MeasurementStatus.PARTIAL : MeasurementStatus.COMPLETE;
    }

    private static ModuleReport moduleReport(Compilation compilation, String name, Ast.Module module) {
        Map<String, List<RowOutcome>> byTarget = new LinkedHashMap<>();
        List<Incompleteness> incompleteness = new ArrayList<>();
        // The same rows every measure beside them reads. Two evaluations of
        // one model can disagree — a row that ran out of time under the instrumented one and held
        // under the other — and a report whose counts came from one while its coverage came from the
        // other would say a case is verified and its arm unreached in the same breath. The findings
        // `--strict` exits on come from these same rows, so the exit code and what is printed agree.
        for (String sourceId : compilation.exampleSourcesOf(name)) {
            Output.Examples.Of observed =
                    compilation.db().ask(Output.Examples.asked(compilation.db(), name, sourceId)).value();
            if (observed == null) {
                // The rows of this source were never evaluated, so nothing here can be counted as
                // covered or as missing. Which is a fact about the measurement, not about the model.
                incompleteness.add(Incompleteness.of(Incompleteness.Code.RUNTIME_ABSENT,
                        Incompleteness.Scope.SOURCE, sourceId));
                continue;
            }
            for (Incompleteness gap : observed.incompleteness()) {
                // One entry per reason. A module-level failure found from each of three attached files
                // is one failure, and a build that counts these should count one.
                if (incompleteness.stream().noneMatch(had -> had.identity().equals(gap.identity()))) {
                    incompleteness.add(gap);
                }
            }
            for (RowOutcome row : observed.rows()) {
                byTarget.computeIfAbsent(row.target(), _ -> new ArrayList<>()).add(row);
            }
        }
        Map<String, Adequacy.SignatureEvidence> signatures =
                compilation.db().ask(new Adequacy.Witnesses(name)).value();
        Map<String, PartitionEvidence> partitions =
                compilation.db().ask(new Adequacy.Coverage(name)).value();
        Map<String, Adequacy.BranchEvidence> branches =
                compilation.db().ask(new Adequacy.BranchCoverage(name)).value();
        // The lines this report prints and the warnings a build is given are the same list, asked for
        // once here. A second reading of the evidence would be a second statement of what a gap is.
        Map<String, List<Adequacy.Finding>> findings =
                compilation.db().ask(new Adequacy.Findings(name)).value();
        List<BehaviorReport> behaviors = new ArrayList<>();
        for (Ast.BehaviorDef behavior : module.behaviors()) {
            List<RowOutcome> rows = byTarget.getOrDefault(behavior.name(), List.of());
            int pending = (int) rows.stream()
                    .filter(r -> r.disposition() == souther.compiler.observe.Disposition.PENDING)
                    .count();
            // Anything larger than a behavior holds this one: a source that could not be evaluated is
            // missing rows for whatever it wrote, and a module whose classes could not be instrumented
            // is missing arms for all of them. The scope says which, so nothing here has to guess.
            boolean unreadable = incompleteness.stream()
                    .anyMatch(i -> i.countsAgainst(behavior.name()));
            Adequacy.SignatureEvidence signature =
                    signatures == null ? null : signatures.get(behavior.name());
            PartitionEvidence partition = partitions == null ? null
                    : partitions.getOrDefault(behavior.name(), PartitionEvidence.NONE);
            // Null where the compile did not get far enough to be asked, which is not a measure that
            // came back with nothing. Every measure that did run says why it has no number.
            Adequacy.BranchEvidence branch =
                    branches == null ? null : branches.get(behavior.name());
            behaviors.add(new BehaviorReport(behavior.name(),
                    ExampleVerifier.isPending(module, behavior.name()), rows.size(), pending,
                    unreadable ? MeasurementStatus.PARTIAL : statusOf(signature, partition, branch),
                    signature, partition, branch,
                    findings == null ? List.of()
                            : findings.getOrDefault(behavior.name(), List.of())));
        }
        MeasurementStatus status = incompleteness.isEmpty()
                ? MeasurementStatus.COMPLETE : MeasurementStatus.PARTIAL;
        for (BehaviorReport behavior : behaviors) {
            status = status.and(behavior.status());
        }
        return new ModuleReport(name, status, incompleteness, behaviors);
    }

    /** This report with only the modules and behaviors the caller asked about. A name that matches
     * nothing leaves an empty report rather than the whole one. */
    public AdequacyReport only(String module, String behavior) {
        List<ModuleReport> kept = new ArrayList<>();
        MeasurementStatus overall = MeasurementStatus.COMPLETE;
        for (ModuleReport m : modules) {
            if (module != null && !module.equals(m.module())) {
                continue;
            }
            List<BehaviorReport> behaviors = behavior == null ? m.behaviors()
                    : m.behaviors().stream().filter(b -> behavior.equals(b.name())).toList();
            // What a filtered report says has to be about what it shows. A reason another behavior
            // could not be measured, carried into a report that does not mention that behavior, is a
            // status nothing in front of the reader accounts for.
            //
            // A reason larger than a behavior stays: a whole source that could not be evaluated is
            // missing rows for whatever it held, this behavior included.
            Set<String> shown = behaviors.stream().map(BehaviorReport::name)
                    .collect(java.util.stream.Collectors.toCollection(LinkedHashSet::new));
            List<Incompleteness> gaps = behavior == null ? m.incompleteness()
                    : m.incompleteness().stream()
                            .filter(gap -> !gap.scope().isOneBehavior()
                                    || shown.contains(gap.subject()))
                            .toList();
            MeasurementStatus status = gaps.isEmpty()
                    ? MeasurementStatus.COMPLETE : MeasurementStatus.PARTIAL;
            for (BehaviorReport shownBehavior : behaviors) {
                status = status.and(shownBehavior.status());
            }
            kept.add(new ModuleReport(m.module(), status, gaps, behaviors));
            overall = overall.and(status);
        }
        return new AdequacyReport(schemaVersion, compilerVersion, askedLevel, overall,
                List.copyOf(kept));
    }

    /** How many rows are recorded and waiting for a {@code let}, across everything reported.
     *
     * <p>Reported and never gated on. Waiting is the normal state of a model being written, and a
     * build that refused one would refuse the practice of recording what an injected behavior owes. */
    public int pendingRows() {
        return modules.stream().flatMap(m -> m.behaviors().stream())
                .mapToInt(BehaviorReport::pending).sum();
    }

    /** Everything the measures found, across everything reported. */
    public List<Adequacy.Finding> findings() {
        return modules.stream().flatMap(m -> m.behaviors().stream())
                .flatMap(b -> b.findings().stream()).toList();
    }

    /** The findings a build is entitled to refuse: an asked measure came to an answer and the answer
     *  was that something the rows are asked for is not there. */
    public List<Adequacy.Finding> adequacyGaps() {
        return findings().stream().filter(Adequacy.Finding::isAdequacyGap).toList();
    }

    /**
     * Whether the rows meet what the asked measures require.
     *
     * <p>Derived on every call rather than held, because {@link #only(String, String)} makes a report
     * of part of this one and a verdict about the whole would be a verdict about behaviors that report
     * does not show.
     *
     * <p>The empty case is answered first. Asking nothing that could find a gap and finding none are
     * not the same answer, and {@code allMatch} over no measures is true.
     */
    public AdequacyStatus adequacy() {
        List<MeasurementStatus> required = requiredMeasures();
        if (required.isEmpty()) {
            return AdequacyStatus.UNDETERMINED;
        }
        if (!adequacyGaps().isEmpty()) {
            return AdequacyStatus.NOT_SATISFIED;
        }
        boolean unread = modules.stream().anyMatch(m -> !m.incompleteness().isEmpty());
        return !unread && required.stream().allMatch(m -> m == MeasurementStatus.COMPLETE)
                ? AdequacyStatus.SATISFIED : AdequacyStatus.UNDETERMINED;
    }

    /**
     * The status of every measure that was asked for and could have found a gap.
     *
     * <p>Which measures those are is what {@code askedLevel} says, and not what the evidence looks
     * like: a behavior whose arms were never asked about and one whose arms could not be measured both
     * carry an {@code UNAVAILABLE} branch, and only the first of them leaves the rows adequate.
     *
     * <p>Whether a measure applies at all is the measure's own answer, and never the shape of what
     * came back. A behavior with no body has no arms, and a position dropped for being past the axis
     * limit left no boundary behind — in both cases the numbers look exactly like a measure that was
     * made and found nothing, so a report reading them back would call the first adequate and the
     * second covered.
     */
    private List<MeasurementStatus> requiredMeasures() {
        List<MeasurementStatus> measures = new ArrayList<>();
        for (ModuleReport module : modules) {
            for (BehaviorReport behavior : module.behaviors()) {
                if (askedLevel.reports() && behavior.signature() != null) {
                    measures.add(behavior.signature().status());
                }
                if (!askedLevel.measuresArms()) {
                    continue;
                }
                if (behavior.branch() != null && behavior.branch().applicable()) {
                    measures.add(behavior.branch().status());
                }
                if (behavior.partition() == null) {
                    continue;
                }
                behavior.partition().boundaries().forEach(b -> measures.add(b.status()));
                // A dropped axis that was carrying a line some rule drew took boundaries with it, and
                // nothing can ask about them now. One that was only classifying took a measure no
                // build refuses over, so it costs a line in the report and not the verdict. The pair
                // space is neither: a combination is not where a boundary comes from.
                if (behavior.partition().omitted().stream()
                        .anyMatch(Partitions.OmittedAxis::carriedAnObligation)) {
                    measures.add(MeasurementStatus.PARTIAL);
                }
            }
        }
        return measures;
    }

    // --- rendering --------------------------------------------------------------------------------

    public String human() {
        StringBuilder out = new StringBuilder();
        int implemented = 0;
        int injected = 0;
        for (ModuleReport module : modules) {
            out.append(String.format("%-56s measurement: %s%n", module.module(),
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
                partition(out, behavior);
                branch(out, behavior);
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
        // Last, and its own line. What the measurement managed is said above, per module; this is the
        // other question, and the two were one word until they disagreed in front of a reader.
        out.append(String.format("adequacy: %s%n",
                adequacy().name().toLowerCase(java.util.Locale.ROOT).replace('_', ' ')));
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
        boolean decided = signature.status() == MeasurementStatus.COMPLETE;
        OutputCaseEvidence output = signature.output();
        if (!output.declared().isEmpty()) {
            out.append(String.format("    signature   out specified %d/%d  observed %d/%d "
                            + " verified %d/%d%s%n",
                    output.specified().size(), output.declared().size(),
                    output.observed().size(), output.declared().size(),
                    output.verified().size(), output.declared().size(),
                    decided ? "" : "   (partial)"));
            for (Adequacy.Finding f : behavior.of(Adequacy.Kind.OUTPUT_CASE_UNSPECIFIED)) {
                out.append(String.format("      · %sexpects `%s`%n", noRow(f), f.args().get(0)));
            }
            for (Adequacy.Finding f : behavior.of(Adequacy.Kind.OUTPUT_CASE_UNVERIFIED)) {
                out.append(String.format("      · %sconfirms `%s`%n", noRow(f), f.args().get(0)));
            }
        }
        for (int i = 0; i < signature.inputs().size(); i++) {
            InputCaseEvidence input = signature.inputs().get(i);
            if (input.declared().isEmpty()) {
                continue;
            }
            // Counted against the cases a row can be written at. A case the body answers `unreachable`
            // for is one the compiler refuses a row for, so leaving it in the denominator would ask
            // for work that cannot be done and hold the model one case short for ever.
            out.append(String.format("                in #%d specified %d/%d%s%n", i + 1,
                    input.specified().size(), input.coverable().size(),
                    input.excluded().isEmpty() ? ""
                            : "   excluded " + input.excluded().size()));
            int position = i + 1;
            for (Adequacy.Finding f : behavior.of(Adequacy.Kind.INPUT_CASE_UNSPECIFIED)) {
                if (f.args().get(1).equals(position)) {
                    out.append(String.format("      · %suses `%s`%n", noRow(f), f.args().get(0)));
                }
            }
            for (TypeName ruled : input.excluded()) {
                out.append(String.format("      · `%s` is declared unreachable%n", ruled.name()));
            }
        }
    }

    /**
     * How a finding names what nothing did, given how far its measure got.
     *
     * <p>Where some rows could not be read, a case nothing here claims is a case nothing *seen*
     * claims. The summary already says partial; each line has to say it too, or the lines read as the
     * finding and the word in the margin as a footnote.
     */
    private static String noRow(Adequacy.Finding finding) {
        return finding.status() == MeasurementStatus.COMPLETE
                ? "no row " : "undecided whether a row ";
    }

    /**
     * The reason the model wrote, where there is one to name.
     *
     * <p>Several reasons are not printed: a class ruled out by a fork whose paths abort for different
     * reasons has no one sentence about it, and picking one would say something the model does not.
     */
    private static String why(PartitionEvidence.ExcludedClass ruled) {
        return ruled.reasons().size() == 1 ? ": " + ruled.reasons().get(0)
                : ruled.reasons().isEmpty() ? "" : " on every path";
    }

    /**
     * How much of what the model distinguishes the rows reach.
     *
     * <p>A boundary a guard drew is printed as not measured rather than as missed. Meeting it takes
     * more than writing the value — the comparison has to have run — and nothing counts that yet.
     */
    private static void partition(StringBuilder out, BehaviorReport behavior) {
        PartitionEvidence partition = behavior.partition();
        if (partition == null || (partition.axes().isEmpty() && partition.boundaries().isEmpty()
                && partition.notDerivable().isEmpty())) {
            return;
        }
        // Counted over the positions that were measured. A position nothing was measured at
        // contributes no classes to the denominator: nought out of two reads as two gaps, and a
        // measure that was never made found none. What the body ruled out is counted over all of
        // them — that is what the model says, and no row has to exist for it to be so.
        List<PartitionEvidence.AxisCoverage> measuredAxes = partition.axes().stream()
                .filter(a -> a.status() != MeasurementStatus.UNAVAILABLE).toList();
        int classes = measuredAxes.stream().mapToInt(a -> a.classes().size()).sum();
        int covered = measuredAxes.stream().mapToInt(a -> a.covered().size()).sum();
        int excluded = partition.axes().stream().mapToInt(a -> a.excluded().size()).sum();
        out.append(String.format("    partition   axes %d   single-axis %d/%d%s%s%s%n",
                partition.axes().size(), covered, classes,
                excluded == 0 ? "" : "   excluded " + excluded,
                notes(partition.axes(), a -> a.status() == MeasurementStatus.UNAVAILABLE,
                        a -> whyNoAxis(a.reason())),
                pairs(partition.pairs())));
        for (Adequacy.Finding f : behavior.of(Adequacy.Kind.AXIS_CLASS_UNCOVERED)) {
            out.append(String.format("      · %s `%s`%n",
                    f.status() == MeasurementStatus.PARTIAL
                            ? "undecided whether a row is in" : "no row is in", f.args().get(0)));
        }
        // Not a finding: nothing is owed here, and what the line says is what the model already
        // decided rather than something the rows left undone.
        for (PartitionEvidence.AxisCoverage axis : partition.axes()) {
            for (PartitionEvidence.ExcludedClass ruled : axis.excluded()) {
                out.append(String.format("      · `%s` is declared unreachable%s%n",
                        ruled.classId(), why(ruled)));
            }
        }
        // Counted where both questions have an answer: the line was measured against the rows, and
        // something has shown a row can be written at it. The two are separate observations and are
        // filtered separately — a line nobody measured and a line nothing promises are not the same
        // absence, and printing them under one sentence said "not known to be writable" about
        // behaviors whose only problem was that nobody had written a row yet.
        List<BoundaryAssessment> measured = partition.boundaries().stream()
                .filter(b -> !(b.coverage() instanceof BoundaryAssessment.Coverage.NotMeasured))
                .filter(b -> b.writability().known()).toList();
        List<BoundaryAssessment> unpromised = partition.boundaries().stream()
                .filter(b -> !b.writability().known()).toList();
        long met = measured.stream().filter(b -> b.coverage().hit()).count();
        long undecided = measured.stream()
                .filter(b -> b.coverage() instanceof BoundaryAssessment.Coverage.Undecided).count();
        out.append(String.format("    boundary    %d/%d%s%s%n", met, measured.size(),
                notes(partition.boundaries(),
                        b -> b.coverage() instanceof BoundaryAssessment.Coverage.NotMeasured,
                        b -> whyNoBoundary(b.coverage())),
                undecided == 0 ? "" : "   (" + undecided + " undecided: a value was not read)"));
        for (Adequacy.Finding f : behavior.of(Adequacy.Kind.BOUNDARY_UNMET)) {
            out.append(String.format("      · no row is at %s = %s (%s)%n",
                    f.args().get(0), f.args().get(1), f.args().get(2)));
        }
        // Said and not counted. Nothing has shown a row can be written at these — the projection
        // could not read every rule of the value, and nothing built one either — so they are not
        // rows anybody is owed, and they are still the only thing there is to say about the
        // position.
        for (BoundaryAssessment b : unpromised) {
            out.append(String.format("      · not known to be writable: %s = %s (%s)%n",
                    b.axis(), b.value(), b.origin()));
        }
        for (Adequacy.Finding f : behavior.of(Adequacy.Kind.PARTITION_NOT_DERIVABLE)) {
            out.append(String.format("      · not derivable: %s%n", f.args().get(0)));
        }
        for (Adequacy.Finding f : behavior.of(Adequacy.Kind.PARTITION_OMITTED)) {
            out.append(String.format("      · omitted: %s (axis limit)%n", f.args().get(0)));
        }
    }

    /**
     * Which arms of the body the rows go through.
     *
     * <p>Called the arms, and never the paths. Going through both arms of two nested conditions is four
     * arms and says nothing about their combinations, and a report that said "paths covered" would
     * invite an author to stop looking exactly where there is more to find.
     */
    private static void branch(StringBuilder out, BehaviorReport behavior) {
        Adequacy.BranchEvidence branch = behavior.branch();
        if (branch == null) {
            return;
        }
        if (branch.status() == MeasurementStatus.UNAVAILABLE) {
            // The measure's own answer, translated. Nothing here works out why from the row count or
            // the kind of behavior: those correlate with the reason and are not it, and the line an
            // author reads is the one place that difference shows.
            String said = switch (branch.reason()) {
                case NO_BODY -> "not applicable (this behavior has no body)";
                case UNREADABLE -> "unavailable (the arms could not be measured)";
                // A build that did not ask, and a behavior nobody wrote a row for, are both quiet.
                // The first is one fact about the run and saying it against every behavior repeats it;
                // the second is what writing a row turns on, and an absence of evidence is not a gap.
                case NOT_ASKED, NO_ROWS -> null;
            };
            if (said != null) {
                out.append(String.format("    branch      %s%n", said));
            }
            return;
        }
        boolean decided = branch.status() == MeasurementStatus.COMPLETE;
        out.append(String.format("    branch      %d/%d%s%n", branch.covered().size(),
                branch.all().size(), decided ? "" : "   (undecided: a row was not read)"));
        // The position alone: an arm is part of a body, and a body is written in the module's own
        // source, which the section this is under already names. Only a row can be somewhere else.
        // Named only where every row was read: an arm a row that never finished might have gone
        // through is undecided, and calling it unreached sends the author after a row that exists.
        if (!decided) {
            return;
        }
        for (Adequacy.Finding f : behavior.of(Adequacy.Kind.ARM_UNREACHED)) {
            out.append(String.format("      · no row goes through `%s` (%s)%n",
                    f.args().get(0), f.at()));
        }
    }

    /**
     * The pair numbers as counts, never as one ratio.
     *
     * <p>A ratio needs a denominator that is known, and this one is not: a combination no row sits in
     * has not been shown unreachable, only untried. Printing 3/8 would read as five gaps when it may
     * be five impossibilities.
     */
    private static String pairs(PartitionEvidence.PairSpace pairs) {
        if (pairs == null || pairs.total() == 0
                || pairs.status() == MeasurementStatus.UNAVAILABLE) {
            return "";
        }
        if (pairs.truncated()) {
            return String.format("   pairs %d, too many to enumerate", pairs.total());
        }
        if (pairs.decided() && pairs.status() == MeasurementStatus.COMPLETE) {
            return String.format("   pairs %d/%d", pairs.covered(), pairs.total());
        }
        // Untried where every row was read, undecided where some were not: a combination an unread row
        // may sit in has not been left untried by anybody.
        return String.format("   pairs %d reached / %d known reachable, %d %s",
                pairs.covered(), pairs.witnessedFeasible(), pairs.unknown(),
                pairs.status() == MeasurementStatus.COMPLETE ? "untried" : "undecided");
    }

    /**
     * How many of a measure's parts have no number, and why, one note per distinct reason.
     *
     * <p>Grouped rather than summed. Two lines left unmeasured for two different reasons are two
     * facts, and one count over both would be a number whose sentence is true of only some of what it
     * counts — which is the shape of the thing this report stopped doing.
     */
    private static <T> String notes(List<T> all, java.util.function.Predicate<T> unmeasured,
                                    java.util.function.Function<T, String> why) {
        Map<String, Long> counted = new LinkedHashMap<>();
        for (T each : all) {
            if (unmeasured.test(each)) {
                counted.merge(why.apply(each), 1L, Long::sum);
            }
        }
        StringBuilder out = new StringBuilder();
        counted.forEach((said, count) ->
                out.append("   (").append(count).append(" not measured: ").append(said).append(')'));
        return out.toString();
    }

    private static String whyNoAxis(PartitionEvidence.AxisCoverage.Reason reason) {
        return switch (reason) {
            case NO_ROWS -> "no row names this behavior";
        };
    }

    private static String whyNoBoundary(BoundaryAssessment.Coverage coverage) {
        if (!(coverage instanceof BoundaryAssessment.Coverage.NotMeasured absent)) {
            return "";
        }
        return switch (absent.reason()) {
            case ARMS_NOT_ASKED -> "the arms were not asked for";
            case ARMS_UNREADABLE -> "the arms could not be measured";
            case NO_ROWS -> "no row names this behavior";
        };
    }

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /**
     * How this report spells an enumerated value on the wire.
     *
     * <p>Here rather than at each field, so that the words a consumer reads have one origin. The
     * shipped schema names the same words in its own file and is held against this — against what is
     * written, not against a second reading of the enum, because those are different things and only
     * one of them is what a consumer sees. A spelling rule applied at ten call sites is ten places for
     * the schema to stop describing the output while every one of them still agrees with the enum.
     */
    public static String word(Enum<?> value) {
        return value.name().toLowerCase(java.util.Locale.ROOT);
    }

    /**
     * The same, for the one field with no enum behind it.
     *
     * <p>Whether a behavior has a {@code let} is a boolean, and these are the two words it is written
     * as. Having no enum is why it needs this more than the others rather than less: nothing else in
     * the compiler says what these words are.
     */
    public static String implementationWord(boolean injected) {
        return injected ? "injected" : "implemented";
    }

    public String json() {
        ObjectNode root = JSON.createObjectNode();
        root.put("schemaVersion", schemaVersion);
        root.put("compilerVersion", compilerVersion);
        root.put("status", word(status));
        root.put("adequacy", word(adequacy()));
        ArrayNode modulesOut = root.putArray("modules");
        for (ModuleReport module : modules) {
            ObjectNode m = modulesOut.addObject();
            m.put("module", module.module());
            m.put("status", word(module.status()));
            ArrayNode gaps = m.putArray("incompleteness");
            for (Incompleteness gap : module.incompleteness()) {
                ObjectNode g = gaps.addObject();
                g.put("code", word(gap.code()));
                g.put("scope", word(gap.scope()));
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
                b.put("implementation", implementationWord(behavior.injected()));
                b.put("rows", behavior.rows());
                b.put("pending", behavior.pending());
                b.put("status", word(behavior.status()));
                signature(b, behavior.signature());
                partition(b, behavior.partition());
                branch(b, behavior.branch());
            }
        }
        return root.toPrettyString();
    }

    private static void signature(ObjectNode behavior, Adequacy.SignatureEvidence signature) {
        if (signature == null) {
            return;
        }
        ObjectNode out = behavior.putObject("signature");
        measured(out, signature.status(), signature.reason());
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
            names(in.putArray("excluded"), input.excluded());
            in.put("unclassifiedRows", input.unclassifiedRows());
        }
    }

    private static void partition(ObjectNode behavior, PartitionEvidence partition) {
        if (partition == null) {
            return;
        }
        ObjectNode out = behavior.putObject("partition");
        ArrayNode axes = out.putArray("axes");
        for (PartitionEvidence.AxisCoverage axis : partition.axes()) {
            ObjectNode a = axes.addObject();
            a.put("axis", axis.axis());
            a.put("path", axis.path());
            axis.classes().forEach(a.putArray("classes")::add);
            axis.covered().stream().sorted().forEach(a.putArray("covered")::add);
            ArrayNode excluded = a.putArray("excluded");
            for (PartitionEvidence.ExcludedClass ruled : axis.excluded()) {
                ObjectNode e = excluded.addObject();
                e.put("class", ruled.classId());
                ruled.reasons().forEach(e.putArray("reasons")::add);
            }
            a.put("unclassifiedRows", axis.unclassifiedRows());
            measured(a, axis.status(), axis.reason());
        }
        ArrayNode boundaries = out.putArray("boundaries");
        for (BoundaryAssessment boundary : partition.boundaries()) {
            ObjectNode b = boundaries.addObject();
            b.put("axis", boundary.axis());
            b.put("origin", boundary.origin());
            b.put("side", word(boundary.side()));
            b.put("value", boundary.value());
            // The shape a published schema promises, read off the assessment rather than stored
            // beside it. What each of these says is unchanged; where it comes from is one answer now
            // instead of two kept in step. Naming which evidence made a line writable is worth
            // emitting and would be a different schema, so it waits for one.
            b.put("hit", boundary.coverage().hit());
            b.put("knownWritable", boundary.writability().known());
            measured(b, boundary.status(), boundary.reason());
        }
        ObjectNode pairs = out.putObject("pairs");
        pairs.put("total", partition.pairs().total());
        pairs.put("covered", partition.pairs().covered());
        pairs.put("witnessedFeasible", partition.pairs().witnessedFeasible());
        pairs.put("provenInfeasible", partition.pairs().provenInfeasible());
        pairs.put("unknown", partition.pairs().unknown());
        pairs.put("truncated", partition.pairs().truncated());
        measured(pairs, partition.pairs().status(), partition.pairs().reason());
        partition.notDerivable().forEach(out.putArray("notDerivable")::add);
        ArrayNode omitted = out.putArray("omitted");
        partition.omitted().forEach(o -> omitted.add(o.reason().subject()));
    }

    private static void branch(ObjectNode behavior, Adequacy.BranchEvidence branch) {
        if (branch == null) {
            return;
        }
        ObjectNode out = behavior.putObject("branch");
        measured(out, branch.status(), branch.reason());
        out.put("arms", branch.all().size());
        out.put("covered", branch.covered().size());
        // Only where every row was read. An arm a row that never finished might have gone through is
        // undecided, and a field called `unreached` holding it says something that is not so — which
        // reading `status` beside it does not undo.
        ArrayNode unreached = out.putArray("unreached");
        List<souther.compiler.coverage.CoverageSites.Site> named =
                branch.status() == MeasurementStatus.COMPLETE ? branch.unreached() : List.of();
        for (souther.compiler.coverage.CoverageSites.Site arm : named) {
            ObjectNode a = unreached.addObject();
            a.put("label", arm.label());
            a.put("kind", word(arm.kind()));
            ObjectNode at = a.putObject("at");
            at.put("sourceId", arm.at().sourceId());
            at.put("line", arm.at().pos().line());
            at.put("column", arm.at().pos().column());
        }
    }

    /**
     * What a measure managed, and where it managed nothing, why.
     *
     * <p>Two fields and not one. {@code status} says whether there is a number; {@code reason} says
     * why there is not, and is absent where there is. A reader that only knows {@code status} reads
     * exactly what it read before, and one that wants to tell a measure nobody asked for from a
     * measure that failed no longer has to work it out from the numbers beside it.
     */
    private static void measured(ObjectNode of, MeasurementStatus status, Enum<?> reason) {
        of.put("status", word(status));
        if (reason != null) {
            of.put("reason", word(reason));
        }
    }

    /** Case names, sorted: a report that changes order between runs cannot be compared between runs,
     * and the sets these come from keep the order the rows happened to arrive in. */
    private static void names(ArrayNode into, java.util.Set<TypeName> cases) {
        cases.stream().map(TypeName::name).sorted().forEach(into::add);
    }
}
