package souther.compiler.report;

import souther.compiler.query.ClaimAnnotations;
import souther.compiler.source.SourceId;

import souther.compiler.ast.Hir;
import souther.compiler.diag.Citation;
import souther.compiler.diag.SourceNameResolver;
import souther.compiler.diag.QuotedFrom;
import souther.compiler.diag.SourcePos;
import souther.compiler.meta.ModuleMetadata;
import souther.compiler.check.Prepared;
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
import souther.compiler.text.DisplayColumns;
import souther.compiler.types.TypeSymbol;

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

    public static final int SCHEMA_VERSION = 2;

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

    public record ModuleReport(String module, SourceId declaredIn, MeasurementStatus status,
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
     * @param claimed   what the body declared cannot arrive, beside the measures rather than in
     *                  them. The two are joined where this report is written and nowhere else,
     *                  which is what keeps a claim from reaching a denominator
     * @param findings  what the measures found and nothing filled, which is what the lines under this
     *                  behavior print and what a build is warned about — one list, read three ways
     */
    public record BehaviorReport(String name, boolean injected, int rows, int pending,
                                 MeasurementStatus status,
                                 Adequacy.SignatureEvidence signature,
                                 PartitionEvidence partition,
                                 ClaimAnnotations claimed,
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
            Prepared module = compilation.module(name);
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

    private static ModuleReport moduleReport(Compilation compilation, String name, Prepared module) {
        Map<String, List<RowOutcome>> byTarget = new LinkedHashMap<>();
        List<Incompleteness> incompleteness = new ArrayList<>();
        // The same rows every measure beside them reads. Two evaluations of
        // one model can disagree — a row that ran out of time under the instrumented one and held
        // under the other — and a report whose counts came from one while its coverage came from the
        // other would say a case is verified and its arm unreached in the same breath. The findings
        // `--strict` exits on come from these same rows, so the exit code and what is printed agree.
        for (SourceId sourceId : compilation.exampleSourcesOf(name)) {
            Output.Examples.Of observed =
                    compilation.db().ask(Output.Examples.asked(compilation.db(), name, sourceId)).value();
            if (observed == null) {
                // The rows of this source were never evaluated, so nothing here can be counted as
                // covered or as missing. Which is a fact about the measurement, not about the model.
                incompleteness.add(Incompleteness.ofSource(
                        Incompleteness.Code.OBSERVATION_ABSENT, sourceId));
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
        // Why the rows a position could not place could not be placed. The count is the axis's and
        // says how much; this says what happened, and joining the two lists is this report's job
        // rather than the coverage's — one of them is a measurement and the other is a reason.
        if (partitions != null) {
            for (PartitionEvidence partition : partitions.values()) {
                for (Incompleteness gap : partition.whyUnclassified()) {
                    if (incompleteness.stream().noneMatch(had -> had.identity().equals(gap.identity()))) {
                        incompleteness.add(gap);
                    }
                }
            }
        }
        Map<String, Adequacy.BranchEvidence> branches =
                compilation.db().ask(new Adequacy.BranchCoverage(name)).value();
        // What each body declared, read where it was judged. Beside the measures and never inside
        // one: this report is where the two are put together.
        Map<String, ClaimAnnotations> claims =
                compilation.db().ask(new souther.compiler.query.Bodies.Claimed(name)).value();
        // The lines this report prints and the warnings a build is given are the same list, asked for
        // once here. A second reading of the evidence would be a second statement of what a gap is.
        Map<String, List<Adequacy.Finding>> findings =
                compilation.db().ask(new Adequacy.Findings(name)).value();
        List<BehaviorReport> behaviors = new ArrayList<>();
        for (Hir.BehaviorDef behavior : module.behaviors()) {
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
                    module.injected(behavior),
                    rows.size(), pending,
                    unreadable ? MeasurementStatus.PARTIAL : statusOf(signature, partition, branch),
                    signature, partition,
                    claims == null ? ClaimAnnotations.NONE
                            : claims.getOrDefault(behavior.name(), ClaimAnnotations.NONE),
                    branch,
                    findings == null ? List.of()
                            : findings.getOrDefault(behavior.name(), List.of())));
        }
        MeasurementStatus status = incompleteness.isEmpty()
                ? MeasurementStatus.COMPLETE : MeasurementStatus.PARTIAL;
        for (BehaviorReport behavior : behaviors) {
            status = status.and(behavior.status());
        }
        return new ModuleReport(name, compilation.sourceIdOf(name), status, incompleteness,
                behaviors);
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
                            .filter(gap -> gap.behavior().map(shown::contains).orElse(true))
                            .toList();
            MeasurementStatus status = gaps.isEmpty()
                    ? MeasurementStatus.COMPLETE : MeasurementStatus.PARTIAL;
            for (BehaviorReport shownBehavior : behaviors) {
                status = status.and(shownBehavior.status());
            }
            kept.add(new ModuleReport(m.module(), m.declaredIn(), status, gaps, behaviors));
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
                    add(measures, behavior.signature().status());
                }
                if (!askedLevel.measuresArms()) {
                    continue;
                }
                add(measures, behavior.branch() == null ? null : behavior.branch().status());
                if (behavior.partition() == null) {
                    continue;
                }
                // The measure answers for itself, and its entries answer for themselves. Read off
                // the entries alone, a measure that derived nothing contributed nothing and a
                // behavior whose every bound sits one type away from the position it takes came out
                // adequate on the strength of a measurement nobody made.
                //
                // The lines only. What the positions are divided into is reported and is not what a
                // build is held to: its gaps arrive as findings, and a position with a bound and no
                // division — an `Int` a rule floors and nothing cuts — is an ordinary shape whose
                // boundary measure is made in full. Holding the verdict open for it would say a
                // model was unmeasured on the strength of the one measure that was.
                add(measures, behavior.partition().bounded().status());
                behavior.partition().boundaries().forEach(b -> add(measures, b.status()));
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

    /**
     * One measure's answer, where it is one the verdict is about.
     *
     * <p>{@link MeasurementStatus#NOT_APPLICABLE} is not. Nothing here was ever going to be measured
     * and no row anybody writes would change it, so counting it would leave every model undetermined
     * for having a behavior that answers a plain number. {@link MeasurementStatus#NOT_MEASURED} is
     * counted and is exactly what stops a verdict of satisfied: it is the case where a gap could have
     * been found and nobody looked.
     */
    private static void add(List<MeasurementStatus> measures, MeasurementStatus status) {
        if (status != null && status != MeasurementStatus.NOT_APPLICABLE) {
            measures.add(status);
        }
    }

    // --- rendering --------------------------------------------------------------------------------

    /**
     * The report as a person reads it, with the sources under the names {@code names} gives them.
     *
     * <p>The names are asked for rather than held. What a report is about is identified by whatever
     * the caller handed its sources over as — an index under a build, a document URI under an editor
     * — and what to call one of them is neither of those: it is the shortest thing that tells this
     * reader's files apart, so it is a fact about the set in front of them. A caller with no names to
     * give says so with {@link SourceNameResolver#identity}, and the ids stand for themselves.
     */
    public String human(SourceNameResolver names) {
        StringBuilder out = new StringBuilder();
        int implemented = 0;
        int injected = 0;
        for (ModuleReport module : modules) {
            out.append(String.format("%s measurement: %s%n",
                    DisplayColumns.padRight(module.module(), 56),
                    module.status().name().toLowerCase(java.util.Locale.ROOT)));
            for (BehaviorReport behavior : module.behaviors()) {
                if (behavior.injected()) {
                    injected++;
                } else {
                    implemented++;
                }
                out.append(String.format("  %s %s rows %-4d pending %d%n",
                        DisplayColumns.padRight(behavior.name(), 24),
                        DisplayColumns.padRight(
                                behavior.injected() ? "injected" : "implemented", 13),
                        behavior.rows(), behavior.pending()));
                signature(out, behavior);
                partition(out, behavior, module.declaredIn(), names);
                branch(out, behavior, module.declaredIn(), names);
                // Under the behavior it names, because a reason printed at the module's foot is
                // read as belonging to whichever behavior came last. That was survivable while the
                // only reasons naming one were rare; a position that could not be read is not.
                said(out, module.incompleteness().stream()
                        .filter(gap -> gap.behavior().map(behavior.name()::equals).orElse(false))
                        .toList(), names);
            }
            said(out, module.incompleteness().stream()
                    .filter(gap -> gap.behavior().isEmpty()).toList(), names);
        }
        int total = implemented + injected;
        out.append(String.format("%n%d %s: %d implemented, %d injected; %d %s waiting for a `let`.%n",
                total, total == 1 ? "behavior" : "behaviors", implemented, injected,
                pendingRows(), pendingRows() == 1 ? "row" : "rows"));
        // Last, and its own line. What the measurement managed is said above, per module; this is the
        // other question, and the two were one word until they disagreed in front of a reader.
        out.append(String.format("adequacy: %s%n",
                adequacy().name().toLowerCase(java.util.Locale.ROOT).replace('_', ' ')));
        // What the mark above means, said by the report that wrote it. The count was said only by
        // `--strict`, on standard error, in a run a reader had to ask for — so a reader of the report
        // alone had a mark with nothing to read it by, and one who did ask got a number pointing at a
        // list with more entries in it than the number.
        //
        // What the mark means and not what a refusal decided. The two are printed one under the other
        // where a build asked to be strict and got a human report, and a legend repeating the verdict
        // would be the same sentence twice with nothing to tell a reader which surface said it.
        List<Adequacy.Finding> refused = adequacyGaps();
        if (!refused.isEmpty()) {
            out.append(String.format("%d %s marked `!`: what a strict build refuses over.%n",
                    refused.size(), refused.size() == 1 ? "gap" : "gaps"));
        }
        return out.toString();
    }

    /** The reasons, in the one shape a reason is printed in wherever it sits. */
    private static void said(StringBuilder out, List<Incompleteness> gaps,
                             SourceNameResolver names) {
        for (Incompleteness gap : gaps) {
            out.append(String.format("    · %s%n", Reasons.said(gap, names)));
        }
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
        if (signature == null) {
            return;
        }
        if (!signature.status().counted()) {
            // A measure with no number says why, the way the arms do. Leaving the line out instead
            // put two behaviors side by side in one report, one measured on four lines and one on
            // three, with nothing saying the fourth did not apply — and hid the fact worth reading,
            // which is that a behavior answering a bare primitive gets less scrutiny than one
            // answering a sum.
            out.append(String.format("    signature   %s%n", switch (signature.reason()) {
                case NOT_A_SUM -> "not applicable (this behavior's output is not a sum)";
                case NO_ROWS -> "not measured (no row names this behavior)";
            }));
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
                out.append(String.format("      %s %sexpects `%s`%n",
                        mark(f), noRow(f), f.args().get(0)));
            }
            for (Adequacy.Finding f : behavior.of(Adequacy.Kind.OUTPUT_CASE_UNVERIFIED)) {
                out.append(String.format("      %s %sconfirms `%s`%n",
                        mark(f), noRow(f), f.args().get(0)));
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
                    out.append(String.format("      %s %suses `%s`%n",
                            mark(f), noRow(f), f.args().get(0)));
                }
            }
            for (TypeSymbol ruled : input.excluded()) {
                out.append(String.format("      · `%s` is declared unreachable%n", ruled.name()));
            }
        }
    }

    /**
     * The mark a finding is printed under, which says what a build does about it.
     *
     * <p>The one thing separating the two kinds of bullet a report prints. Without it four findings
     * of one shape were printed and three of them failed a build, and a reader deciding what to write
     * next either wrote rows for all four — more than the build asks, on a measure the language
     * deliberately chose not to gate — or wrote one and ran again to find out which.
     *
     * <p>Read off the finding's own answer. Reading the kinds again here would be a second
     * classification to keep in step with the one a build refuses on, and the two would agree until
     * a kind changed sides.
     */
    private static String mark(Adequacy.Finding finding) {
        return finding.isAdequacyGap() ? "!" : "·";
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

    /** The positions this report has an axis for, which is what tells a claim it can print beside
     *  one from a claim it has to name a position for. */
    private static List<String> measuredPaths(PartitionEvidence partition) {
        return partition.axes().stream().map(PartitionEvidence.AxisCoverage::path).toList();
    }

    /** The model's own words for a claim, where there is one to print. */
    private static String because(List<String> reasons) {
        return reasons.size() == 1 ? ": " + reasons.get(0)
                : reasons.isEmpty() ? "" : " on every path";
    }

    /** What a reader is told about a claim nothing settled, in this report's own words. */
    private static String unproven(ClaimAnnotations.Why why) {
        return switch (why) {
            case A_RULE_WENT_UNREAD -> "a rule about this position went unread";
            case THE_RULES_LEAVE_THE_POSITION_NOTHING ->
                    "the rules leave this position no value at all";
            case NOTHING_WAS_READ_ABOUT_THE_CASE -> "nothing was read about this case";
            case THE_FORK_IS_NOT_KNOWN_TO_BE_REACHED ->
                    "this arm is inside another, and what reaches it is not read here";
        };
    }

    /**
     * How much of what the model distinguishes the rows reach.
     *
     * <p>A boundary a guard drew is printed as not measured rather than as missed. Meeting it takes
     * more than writing the value — the comparison has to have run — and nothing counts that yet.
     */
    private static void partition(StringBuilder out, BehaviorReport behavior,
                                  SourceId declaredIn, SourceNameResolver names) {
        PartitionEvidence partition = behavior.partition();
        if (partition == null || (partition.axes().isEmpty() && partition.boundaries().isEmpty()
                && partition.notDerivable().isEmpty() && behavior.claimed().all().isEmpty())) {
            return;
        }
        if (!partition.partitioned().status().counted()) {
            // A measure with no number says why, rather than showing a nought that reads as a
            // measurement. `axes 0   single-axis 0/0` was the same three characters a behavior gets
            // when every position it has was measured and every class covered.
            out.append(String.format("    partition   %s%n",
                    whyNoPartition(partition.partitioned().reason())));
        } else {
            // Counted over the positions that were measured. A position nothing was measured at
            // contributes no classes to the denominator: nought out of two reads as two gaps, and a
            // measure that was never made found none.
            List<PartitionEvidence.AxisCoverage> measuredAxes = partition.axes().stream()
                    .filter(a -> a.status().counted()).toList();
            int classes = measuredAxes.stream().mapToInt(a -> a.classes().size()).sum();
            int covered = measuredAxes.stream().mapToInt(a -> a.covered().size()).sum();
            // Over the positions this line counts and no others. A claim about a position past the
            // axis limit is said further down, under its own name — counted here it would be a
            // number taken out of a denominator that never held it.
            int excluded = (int) measuredAxes.stream()
                    .flatMap(each -> behavior.claimed().at(each.path()).stream())
                    .filter(ClaimAnnotations.Said::settled).count();
            out.append(String.format("    partition   axes %d   single-axis %d/%d%s%s%s%n",
                    partition.axes().size(), covered, classes,
                    excluded == 0 ? "" : "   excluded " + excluded,
                    notes(partition.axes(), a -> !a.status().counted(),
                            a -> whyNoAxis(a.reason())),
                    pairs(partition.pairs())));
            for (Adequacy.Finding f : behavior.of(Adequacy.Kind.AXIS_CLASS_UNCOVERED)) {
                out.append(String.format("      %s %s `%s`%n", mark(f),
                        f.status() == MeasurementStatus.PARTIAL
                                ? "undecided whether a row is in" : "no row is in", f.args().get(0)));
            }
            // Not a finding: nothing is owed here, and what the line says is what the model already
            // decided rather than something the rows left undone.
            for (PartitionEvidence.AxisCoverage axis : partition.axes()) {
                for (ClaimAnnotations.Said said : behavior.claimed().at(axis.path())) {
                    // A case out of the denominator says what the author wrote about it; one still
                    // counted says that too, and that nothing settled it — a reader is told both
                    // rather than left to find out by writing the row.
                    out.append(said.settled()
                            ? String.format("      · `%s` is declared unreachable%s%n",
                                    said.classId(), because(said.reasons()))
                            : String.format("      · `%s` is declared unreachable%s, and nothing"
                                            + " here proves it: %s%n",
                                    said.classId(), because(said.reasons()), unproven(said.why())));
                }
            }
        }
        // And the claims about positions this report has no axis for, named by their position since
        // there is no axis above them to have said which one it is. Outside the arm above, because
        // a claim is not a number: a behavior whose positions were all dropped or never read has
        // nothing to count and the same claims to answer for, and printing them only beside a count
        // is how a verdict came to be reached and then not said.
        for (ClaimAnnotations.Said said : behavior.claimed().notAt(measuredPaths(partition))) {
            out.append(said.settled()
                    ? String.format("      · `%s` at `%s` is declared unreachable%s%n",
                            said.classId(), said.at(), because(said.reasons()))
                    : String.format("      · `%s` at `%s` is declared unreachable%s, and nothing"
                                    + " here proves it: %s%n",
                            said.classId(), said.at(), because(said.reasons()),
                            unproven(said.why())));
        }
        undivided(out, behavior);
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
        if (!partition.bounded().status().counted()) {
            // `0/0` said the rows were at every line there was. What it meant was that nobody found
            // a line to be at, which a model whose bounds sit one type away from the position the
            // behavior takes has, and which is the shape of every behavior that validates raw input.
            out.append(String.format("    boundary    %s%n",
                    whyNoBoundary(partition.bounded().reason())));
        } else {
            out.append(String.format("    boundary    %d/%d%s%s%n", met, measured.size(),
                    notes(partition.boundaries(),
                            b -> b.coverage() instanceof BoundaryAssessment.Coverage.NotMeasured,
                            b -> whyNoBoundary(b.coverage())),
                    undecided == 0 ? "" : "   (" + undecided + " undecided: a value was not read)"));
        }
        for (Adequacy.Finding f : behavior.of(Adequacy.Kind.BOUNDARY_UNMET)) {
            // The rule as this report writes it. The finding carries the rule and not words about
            // it, because what to say differs between here — where a file has a name — and the
            // warning built from the same finding, where nothing knows what to call one.
            out.append(String.format("      %s no row is at %s = %s (%s)%n",
                    mark(f), f.args().get(0), f.args().get(1),
                    ((souther.compiler.partition.OriginRef) f.args().get(2))
                            .describe(names, declaredIn)));
        }
        // Said and not counted. Nothing has shown a row can be written at these — the projection
        // could not read every rule of the value, and nothing built one either — so they are not
        // rows anybody is owed, and they are still the only thing there is to say about the
        // position.
        for (BoundaryAssessment b : unpromised) {
            // What the search came to, beside the verdict it did not decide. Whether this edge is
            // counted turns on whether a concrete value was accepted at it, so a reader looking at
            // two models that differ here is looking at what the compiler could establish — and
            // without this line the difference reads as the tool being arbitrary.
            out.append(String.format("      · not known to be writable: %s = %s (%s)%s%n",
                    b.axis(), b.value(), b.origin(names, declaredIn),
                    whatWasTried(b.attempt())));
        }
    }

    /**
     * What the classes measure could not say, said under the classes measure.
     *
     * <p>Under the line these are about, which is the partition and not the boundary. A comparison
     * between two positions divides neither of them and draws a line all the same, so the note saying
     * the position went undivided sat two rows under a boundary count that was counting the line that
     * very comparison drew — one measure's silence printed as though it were the other's.
     */
    private static void undivided(StringBuilder out, BehaviorReport behavior) {
        for (Adequacy.Finding f : behavior.of(Adequacy.Kind.PARTITION_NOT_DERIVABLE)) {
            out.append(String.format("      %s not derivable: %s%n", mark(f), f.args().get(0)));
        }
        // Said apart from the line above it, which is the whole of what this pair is for: one names
        // a position the model divides no way, and this one a position nobody has established
        // anything about.
        for (Adequacy.Finding f : behavior.of(Adequacy.Kind.PARTITION_NOT_READ)) {
            out.append(String.format("      %s not read: %s (%s)%n",
                    mark(f), f.args().get(0), f.args().get(1)));
        }
        // And a third thing, said apart from both: a rule written about a position the axes did
        // measure that nothing took in. The classes beside it are what the model was read to say,
        // and this rule may yet refuse one of them — which is a different thing to act on from a
        // position nothing established anything about. Named by the rule, since a position is not
        // what an author edits.
        for (Adequacy.Finding f : behavior.of(Adequacy.Kind.PARTITION_RULES_NOT_REACHED)) {
            out.append(String.format("      %s rules not reached: %s%n", mark(f), f.args().get(0)));
        }
        for (Adequacy.Finding f : behavior.of(Adequacy.Kind.PARTITION_RULE_UNACCOUNTED)) {
            out.append(String.format("      %s not accounted for: %s — %s %s%n",
                    mark(f), f.args().get(1), f.args().get(2), f.args().get(0)));
        }
        for (Adequacy.Finding f : behavior.of(Adequacy.Kind.PARTITION_OMITTED)) {
            out.append(String.format("      %s omitted: %s (axis limit)%n",
                    mark(f), f.args().get(0)));
        }
    }

    /**
     * Which arms of the body the rows go through.
     *
     * <p>Called the arms, and never the paths. Going through both arms of two nested conditions is four
     * arms and says nothing about their combinations, and a report that said "paths covered" would
     * invite an author to stop looking exactly where there is more to find.
     */
    private static void branch(StringBuilder out, BehaviorReport behavior,
                               SourceId declaredIn, SourceNameResolver names) {
        Adequacy.BranchEvidence branch = behavior.branch();
        if (branch == null) {
            return;
        }
        if (!branch.status().counted()) {
            // The measure's own answer, translated. Nothing here works out why from the row count or
            // the kind of behavior: those correlate with the reason and are not it, and the line an
            // author reads is the one place that difference shows.
            String said = switch (branch.reason()) {
                case NO_BODY -> "not applicable (this behavior has no body)";
                case UNREADABLE -> "not measured (the arms could not be read)";
                case NO_ROWS -> "not measured (no row names this behavior)";
                // The one measure a report says nothing about, because it is not a measure of this
                // report: what was asked for is an input to the whole run, and a line repeating it
                // against every behavior says one fact as many times as the module has behaviors.
                // Every other way of having no number is about this behavior and is said here.
                case NOT_ASKED -> null;
            };
            if (said != null) {
                out.append(String.format("    branch      %s%n", said));
            }
            return;
        }
        boolean decided = branch.status() == MeasurementStatus.COMPLETE;
        out.append(String.format("    branch      %d/%d%s%n", branch.coveredObligations(),
                branch.obligations(), decided ? "" : "   (undecided: a row was not read)"));
        // The position alone where the arm is in the module's own source, which the section this is
        // under already names. It is not always: a body is spliced into whatever calls it, so an arm
        // written in a helper another module declares is in that module's file, and there the file is
        // named with it. Named only where every row was read: an arm a row that never finished might
        // have gone through is undecided, and calling it unreached sends the author after a row that
        // exists.
        if (!decided) {
            return;
        }
        for (Adequacy.Finding f : behavior.of(Adequacy.Kind.ARM_UNREACHED)) {
            out.append(String.format("      %s no row goes through `%s` (%s)%n",
                    mark(f), ArmVocabulary.label(armOf(f)), f.at().said(names, declaredIn)));
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
                || !pairs.status().counted()) {
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

    private static String whyNoPartition(PartitionEvidence.Partitioned.Reason reason) {
        return switch (reason) {
            case NO_AXIS_DERIVED -> "not measured (no partition axis was derived at any position)";
            case NO_SUBJECT -> "not applicable (this behavior is measured at its stages)";
        };
    }

    private static String whyNoBoundary(PartitionEvidence.Bounded.Reason reason) {
        return switch (reason) {
            case NO_LINES_DERIVED -> "not measured (no line was derived at any position)";
            case NO_SUBJECT -> "not applicable (this behavior is measured at its stages)";
        };
    }

    /** What the search for a value at an edge came to, where it ran and found none. */
    private static String whatWasTried(BoundaryAssessment.Attempt attempt) {
        if (!(attempt instanceof BoundaryAssessment.Attempt.Unresolved left)) {
            return "";   // nothing ran, and what a run would have said is not this line's to guess
        }
        return " — nothing composed one: " + left.why().said()
                .orElseGet(() -> whyUnresolved(left.why()));
    }

    /** The category a search came back with, where the class it was about said nothing itself. */
    private static String whyUnresolved(souther.compiler.partition.Generator.UnresolvedCombination why) {
        String at = why.subject();
        return switch (why.reason()) {
            case NOTHING_COMPOSES_ONE -> "nothing here could build a representative for " + at;
            case ALL_CANDIDATES_REJECTED -> "every value tried at " + at + " was refused";
            case SEARCH_LIMIT -> "the search stopped before reaching " + at;
            case NOTHING_TO_BUILD_AGAINST -> "there was nothing to build a candidate against";
            case LINKAGE_FAILED -> "the generated classes would not link";
            case NO_REASON_RECORDED -> "nothing was recorded about why";
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

    /**
     * The word a document writes for how far a position's rules were read.
     *
     * <p>Here rather than at the one place it is written, so a reader holding the arms can be held
     * to the words without reading the writer. No {@code default}: an arm added and not given a
     * word stops the compile rather than arriving in a document as one that already existed.
     */
    public static String readingWord(PartitionEvidence.AxisCoverage.Reading read) {
        // Partial covers both, and what is written beside it says which. A reader keying on the
        // word is told the numbers rest on something unfinished, which is what the word is for; the
        // two facts under it are not exclusive and each has a key of its own.
        return read.answered() ? "complete" : "partial";
    }

    /**
     * The report as a build reads it, explaining the source identities it carries.
     *
     * <p>The names are asked for here for the reason {@link #human} asks for them, and are put to a
     * different use. What this document says about a source is said with the identity the caller
     * handed the source over as, because that is what this compilation refers to the source by, and
     * so what makes two reasons about one file the same reason. A name is not that: it is chosen from
     * the files in front of a reader, so it says what to show and not which source.
     * That leaves the document unreadable on its own — a position in a list says nothing to anyone who
     * does not also hold the list — so the identities are written and the {@code sources} table says
     * what each of them was, and a consumer holding neither the argument list nor the editor's
     * documents can still say which file a reason is about.
     *
     * <p>Which identities get an entry is not decided here. Everything that writes one asks
     * {@link DocumentSources} for the string to write, so the table is what the document turned out to
     * carry rather than a second list of the places an identity can appear.
     */
    public String json(SourceNameResolver names) {
        DocumentSources sources = new DocumentSources(names);
        ObjectNode root = JSON.createObjectNode();
        root.put("schemaVersion", schemaVersion);
        root.put("compilerVersion", compilerVersion);
        root.put("status", wire(status));
        root.put("adequacy", word(adequacy()));
        ArrayNode modulesOut = root.putArray("modules");
        for (ModuleReport module : modules) {
            ObjectNode m = modulesOut.addObject();
            m.put("module", module.module());
            m.put("status", wire(module.status()));
            ArrayNode gaps = m.putArray("incompleteness");
            for (Incompleteness gap : module.incompleteness()) {
                ObjectNode g = gaps.addObject();
                g.put("code", word(gap.code()));
                g.put("scope", word(gap.scope()));
                // What the subject is, is the reason's answer; that this document has now written an
                // identity down and owes an account of it is this renderer's. The two are asked and
                // answered in that order, and neither side holds the other's half.
                g.put("subject",
                        gap.sourceIdentity().map(sources::written).orElseGet(gap::subject));
                gap.at().ifPresent(where -> at(g, where, sources));
            }
            ArrayNode behaviors = m.putArray("behaviors");
            for (BehaviorReport behavior : module.behaviors()) {
                ObjectNode b = behaviors.addObject();
                b.put("name", behavior.name());
                b.put("implementation", implementationWord(behavior.injected()));
                b.put("rows", behavior.rows());
                b.put("pending", behavior.pending());
                b.put("status", wire(behavior.status()));
                signature(b, behavior.signature());
                partition(b, behavior.partition(), behavior.claimed(), sources);
                branch(b, behavior.branch(), sources);
                findings(b, behavior, sources);
            }
        }
        // Last, because what it explains is what was written above it. Where a field sits in an
        // object is nothing a reader of JSON reads, and collecting the identities first would mean
        // walking the report twice to learn what writing it says anyway.
        ObjectNode table = root.putObject("sources");
        sources.table().forEach(table::put);
        return root.toPrettyString();
    }

    /**
     * Where in which source, written once for everything that says it.
     *
     * <p>One writer for the shape, so that a source identity has one way into this document. It was
     * spelled out at each of the two places that point into a source, which is two places to write a
     * position and a line and two places to know that the id needs explaining — and a third would
     * have been written the way the first two were.
     *
     * <p>{@code writtenAt} says what the numbers beside it are. They are where this compile met the
     * code, which is where the code is written for everything read from a source this compile holds
     * and is a call in the caller's file for a body spliced in from one it does not. A consumer
     * handed the numbers alone was told an arm of {@code List.filter} is at {@code m.sou:15:23}. The
     * words come from the citation itself, so this document and the JSON a diagnostic is read from
     * say it the same way.
     */
    private static void at(ObjectNode into, Citation where, DocumentSources sources) {
        ObjectNode at = into.putObject("at");
        SourcePos pos = switch (where) {
            case Citation.Written written -> written.at();
            case Citation.Reached reached -> reached.at();
            case Citation.Unplaced _, Citation.UnplacedElsewhere _, Citation.OutOfSight _ ->
                    throw new NoPlaceToWrite(where);
        };
        if (!(pos.quotedFrom() instanceof QuotedFrom.ASourceThisCompileHolds(SourceId file))) {
            throw new NoPlaceToWrite(where);
        }
        at.put("sourceId", sources.written(file));
        at.put("line", pos.line());
        at.put("column", pos.column());
        ObjectNode writtenAt = at.putObject("writtenAt");
        where.writtenAtFields().forEach(writtenAt::put);
    }

    /**
     * A place this document was asked to write that names no file.
     *
     * <p>The shipped schema says a place has a source, a line and a column, and there are two ways
     * to arrive here without one. A position in a text this compilation cannot name, in a document
     * about a compile whose every source is named, is a position a pass minted rather than read — the
     * open question about whether such a position is a place at all. And a position inside a module's
     * own published text is a real place in a text no reader holds, which the contract has no shape
     * for: not a source, a line and a column, and not nothing either, since what a reader is owed
     * there is which module the code is in.
     *
     * <p>A refusal rather than a document with the fields left out or filled in from whatever file
     * was to hand. Both of those are documents the shipped schema forbids, written silently and read
     * by a build that trusted the version on them. Widening what a consumer must handle is a
     * decision about the contract, and it is not one to take by writing a field.
     *
     * <p>So what this says is that the decision has not been taken. It is loud on purpose: over this
     * compiler's own suite the places written here are eight, all of them in files it holds, which
     * is far too few to read as "this cannot happen".
     */
    static final class NoPlaceToWrite extends IllegalArgumentException
            implements souther.compiler.diag.TheCompilerDisagreesWithItself {

        private static final long serialVersionUID = 1L;

        NoPlaceToWrite(Citation where) {
            super("an adequacy document writes places in files this compile holds, and was given "
                    + where);
        }
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

    private static void partition(ObjectNode behavior, PartitionEvidence partition,
                                  ClaimAnnotations claimed, DocumentSources sources) {
        if (partition == null) {
            return;
        }
        ObjectNode out = behavior.putObject("partition");
        // Each measure's own answer, beside the entries it answered with. Read off the arrays alone,
        // a reader has the same two empties this report used to confuse: a behavior with no
        // positions to divide and one whose positions could not be read both write `[]`, and only
        // this says which. `branch` has carried its own status from the first version; these two are
        // the same measure-level fact in the one place that had nowhere to put it.
        measured(out.putObject("axesMeasure"),
                partition.partitioned().status(), partition.partitioned().reason());
        measured(out.putObject("boundariesMeasure"),
                partition.bounded().status(), partition.bounded().reason());
        ArrayNode axes = out.putArray("axes");
        for (PartitionEvidence.AxisCoverage axis : partition.axes()) {
            ObjectNode a = axes.addObject();
            a.put("axis", axis.axis());
            a.put("path", axis.path());
            // How far the rules about this position were read, beside the classes it came to. A
            // class arrived at from part of the rules is a value the model singled out, and a rule
            // that went unread may yet refuse it — so a consumer holding these classes is told what
            // they rest on rather than left to take them for a set every member of which stands.
            // Its own words, not the ones a measure uses. `status` and `reason` say elsewhere in
            // this document whether a number was arrived at and why there is none; this says how
            // far a reading got, which is a different question about a position that has numbers.
            // Under one pair of keys a consumer would read one as the other.
            ObjectNode read = a.putObject("read");
            read.put("extent", readingWord(axis.read()));
            if (axis.read().reach() == PartitionEvidence.AxisCoverage.Reach.SOME_OUT_OF_SIGHT) {
                read.put("rulesNotReached", true);
            }
            if (!axis.read().unanswered().isEmpty()) {
                ArrayNode standing = read.putArray("unanswered");
                for (PartitionEvidence.AxisCoverage.Unanswered each : axis.read().unanswered()) {
                    ObjectNode one = standing.addObject();
                    one.put("rule", each.rule());
                    one.put("question", word(each.question()));
                    one.put("subject", each.subject());
                }
            }
            axis.classes().forEach(a.putArray("classes")::add);
            axis.covered().stream().sorted().forEach(a.putArray("covered")::add);
            ArrayNode excluded = a.putArray("excluded");
            ArrayNode unproven = a.putArray("unprovenClaims");
            for (ClaimAnnotations.Said said : claimed.at(axis.path())) {
                ObjectNode e = (said.settled() ? excluded : unproven).addObject();
                e.put("class", said.classId());
                said.reasons().forEach(e.putArray("reasons")::add);
                if (!said.settled()) {
                    e.put("why", word(said.why()));
                }
            }
            a.put("unclassifiedRows", axis.unclassifiedRows());
            measured(a, axis.status(), axis.reason());
        }
        ArrayNode offAxis = out.putArray("claimsOffAxis");
        for (ClaimAnnotations.Said said : claimed.notAt(measuredPaths(partition))) {
            ObjectNode c = offAxis.addObject();
            c.put("at", said.at());
            c.put("class", said.classId());
            said.reasons().forEach(c.putArray("reasons")::add);
            if (!said.settled()) {
                c.put("why", word(said.why()));
            }
        }
        ArrayNode boundaries = out.putArray("boundaries");
        for (BoundaryAssessment boundary : partition.boundaries()) {
            ObjectNode b = boundaries.addObject();
            b.put("axis", boundary.axis());
            // The identity, and never left out. This document says what it is about with the
            // ids the caller handed its sources over as, and `sources` explains each one; a
            // display name written here would be a file nothing in the document maps back.
            //
            // No section to leave it out against, either. A person reads a line under a heading
            // that names the module and takes the file from there; a document has no heading, so
            // a place written without its source is a line and a column belonging to nothing —
            // and where a boundary is the only place a report points at, the `sources` table has
            // no other entry to guess from.
            b.put("origin", boundary.origin(sources::written, null));
            b.put("side", word(boundary.side()));
            // What the line is a line at, said rather than left to be inferred from the text beside
            // it. A line between two positions writes the other position where a line at a count
            // writes the count, and the two read alike.
            b.put("kind", word(boundary.shape()));
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
        // Both arrays either way. An absent one and an empty one read the same to a person and not
        // to a reader that checks whether the field is there, and this document's shape is what the
        // schema is written against.
        ArrayNode undivided = out.putArray("notDerivable");
        ArrayNode unread = out.putArray("notRead");
        partition.notDerivable().forEach(each -> {
            if (each.isAbsent()) {
                undivided.add(each.at().toString());
            }
        });
        // The position and what stopped it, kept as the product they are. Which limit a position is
        // waiting on is the thing this list was added to say, and a document that named only the
        // position would leave a consumer to guess it back.
        //
        // Asked of the one reading both surfaces write from. Written from the undivided positions
        // alone, this list was short of every rule left unread at a position the axes went on to
        // measure — which a person reading the report was shown and a consumer keyed on this
        // document was not.
        partition.notRead().forEach(each -> {
            ObjectNode said = unread.addObject();
            said.put("position", each.at());
            said.put("reason", word(each.reason()));
        });
        ArrayNode omitted = out.putArray("omitted");
        partition.omitted().forEach(o -> omitted.add(o.axis().toString()));
    }

    private static void branch(ObjectNode behavior, Adequacy.BranchEvidence branch,
                               DocumentSources sources) {
        if (branch == null) {
            return;
        }
        ObjectNode out = behavior.putObject("branch");
        measured(out, branch.status(), branch.reason());
        out.put("arms", branch.obligations());
        out.put("covered", branch.coveredObligations());
        // Only where every row was read. An arm a row that never finished might have gone through is
        // undecided, and a field called `unreached` holding it says something that is not so — which
        // reading `status` beside it does not undo.
        ArrayNode unreached = out.putArray("unreached");
        List<souther.compiler.coverage.CoverageSites.Site> named =
                branch.status() == MeasurementStatus.COMPLETE ? branch.unreached() : List.of();
        for (souther.compiler.coverage.CoverageSites.Site arm : named) {
            ObjectNode a = unreached.addObject();
            a.put("label", ArmVocabulary.label(arm));
            a.put("kind", word(arm.name()));
            // What the arm is an outcome of. Two fields because the meaning is the pair: an `else`
            // an author wrote under an `if` and one written under a `guard` are the same outcome of
            // two constructs, and a consumer told only the outcome cannot tell them apart.
            a.put("construct", word(arm.construct()));
            at(a, arm.at(), sources);
        }
    }

    /**
     * Everything the measures found about one behavior, and what a build does about each of it.
     *
     * <p>One array and not a field on each measure. Of the kinds a build refuses over, one was
     * already written here under a name of its own and the other three were left to be worked out
     * from the arrays — a case out of {@code declared} and not out of {@code specified}, a boundary
     * whose {@code hit} is false — so a consumer wanting the ones a build refuses over had to
     * reimplement the classification the compiler had already made. Marking each of those in its own
     * place would be the same field written in five, and a sixth kind would have been written the way
     * the five were.
     *
     * <p>Nothing here is a second reading of what is above it. {@code branch.unreached} and
     * {@code boundaries} keep saying what they say, in their own words and about their own measure;
     * this says which findings there are and what a build does about each, which is neither
     * measure's question and was nobody's.
     *
     * <p>A place is written where the finding has one of its own, which is the arms and nothing else.
     * The rest are cited at the behavior's own declaration, so writing it would repeat one coordinate
     * under every finding of a behavior the entry already names — and where the finding is about a
     * line or a class, that coordinate is not where the reader would go.
     */
    private static void findings(ObjectNode behavior, BehaviorReport of, DocumentSources sources) {
        ArrayNode out = behavior.putArray("findings");
        for (Adequacy.Finding finding : of.findings()) {
            ObjectNode f = out.addObject();
            f.put("kind", word(finding.kind()));
            f.put("disposition", word(finding.disposition()));
            f.put("subject", subject(finding));
            // Present where the kind has one. A finding a build is not told about under any code is
            // not one with an empty code, and a consumer joining these to the diagnostics a build
            // printed reads the difference.
            finding.code().ifPresent(code -> f.put("code", code.name()));
            Citation place = placeOfItsOwn(finding);
            if (place != null) {
                at(f, place, sources);
            }
        }
    }

    /**
     * Where a finding is, for the kinds whose place is not the declaration they are under.
     *
     * <p>An arm's, and no other's. A behavior with two {@code guard}s writes two arms labelled
     * {@code else}, and the label is what a finding's subject is — so two findings of one behavior
     * came out identical in every field, and which of them a reader was being told about could not be
     * worked out from the document at all. The place is what {@code branch.unreached} already tells
     * them apart by, and it is written here in the same shape, so the two join.
     *
     * <p>The other eight are cited at the declaration the entry sits under. Writing that coordinate
     * would say where the behavior is, under a finding about a line the model draws or a class of an
     * input — neither of which is there.
     *
     * <p>A switch and not a look at the citation. Whether a finding's place is its own is a fact
     * about the kind, and reading it back off a coordinate would be this report working out something
     * the measure already knew.
     */
    private static Citation placeOfItsOwn(Adequacy.Finding finding) {
        return switch (finding.kind()) {
            case ARM_UNREACHED -> finding.at();
            case OUTPUT_CASE_UNSPECIFIED, OUTPUT_CASE_UNVERIFIED, INPUT_CASE_UNSPECIFIED,
                    AXIS_CLASS_UNCOVERED, BOUNDARY_UNMET, PARTITION_NOT_DERIVABLE,
                    PARTITION_NOT_READ, PARTITION_RULE_UNACCOUNTED, PARTITION_RULES_NOT_REACHED,
                            PARTITION_OMITTED -> null;
        };
    }

    /**
     * What one finding is about, in the one field every kind writes it in.
     *
     * <p>Spelled here per kind rather than taken from the arguments in order. The arguments are the
     * message's, and a document handing a consumer a positional list of them would publish the shape
     * of a sentence — which changes when the sentence is reworded, and says nothing about which of
     * the entries is the subject.
     *
     * <p>Written to join what is already in the document: a class name is one of an axis's
     * {@code classes}, an arm's label is one in {@code branch.unreached}, and an axis and a value
     * name a {@code boundaries} entry. An input's case carries its position with it, because two
     * parameters of one type give two findings a class name alone cannot tell apart.
     */
    private static String subject(Adequacy.Finding finding) {
        List<Object> args = finding.args();
        return switch (finding.kind()) {
            // The label and not the arm, and the same label `branch.unreached` writes: this field
            // exists to join to that entry, and a value spelled a second way here would join to
            // nothing.
            case ARM_UNREACHED -> ArmVocabulary.label(armOf(finding));
            case OUTPUT_CASE_UNSPECIFIED, OUTPUT_CASE_UNVERIFIED, AXIS_CLASS_UNCOVERED,
                    PARTITION_NOT_DERIVABLE, PARTITION_NOT_READ,
                    PARTITION_RULES_NOT_REACHED, PARTITION_OMITTED ->
                    String.valueOf(args.get(0));
            // The rule and what it was left saying. Named by the position alone, two rules nothing
            // took in at one position serialised as two identical objects, and the human line named
            // them while a consumer of the document could not tell them apart.
            case PARTITION_RULE_UNACCOUNTED ->
                    args.get(1) + " — " + args.get(2) + " " + args.get(0);
            case INPUT_CASE_UNSPECIFIED ->
                    String.valueOf(args.get(0)) + " (in #" + args.get(1) + ")";
            case BOUNDARY_UNMET -> args.get(0) + " = " + args.get(1);
        };
    }

    /** The arm an arm finding carries, which it holds as itself so that each reader names it its
     *  own way. */
    private static souther.compiler.coverage.CoverageSites.Site armOf(Adequacy.Finding finding) {
        return (souther.compiler.coverage.CoverageSites.Site) finding.args().get(0);
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
        of.put("status", wire(status));
        if (reason != null) {
            of.put("reason", word(reason));
        }
    }

    /**
     * What a document calls a status, which is not what the compiler calls it.
     *
     * <p>The schema's word for a measure with no number is {@code unavailable}, and which of the two
     * kinds it is, is what the {@code reason} beside it says (spec §example-report-vocabulary). Written
     * out here rather than taken off the enum's own name, so that naming a state inside the compiler
     * is never a change to what a document says. The last time these two were the same string, a
     * field of the schema was whatever the enum happened to be called that week.
     */
    public static String wire(MeasurementStatus status) {
        return switch (status) {
            case COMPLETE -> "complete";
            case PARTIAL -> "partial";
            case NOT_APPLICABLE, NOT_MEASURED -> "unavailable";
        };
    }

    /** Case names, sorted: a report that changes order between runs cannot be compared between runs,
     * and the sets these come from keep the order the rows happened to arrive in. */
    private static void names(ArrayNode into, java.util.Set<TypeSymbol> cases) {
        cases.stream().map(TypeSymbol::name).sorted().forEach(into::add);
    }
}
