package souther.compiler.report;

import souther.compiler.query.ClaimAnnotations;
import souther.compiler.source.SourceId;

import souther.compiler.ast.Hir;
import souther.compiler.check.BehaviorImplementation;
import souther.compiler.diag.Citation;
import souther.compiler.diag.SourceNameResolver;
import souther.compiler.diag.QuotedFrom;
import souther.compiler.diag.SourcePos;
import souther.compiler.meta.ModuleMetadata;
import souther.compiler.check.Prepared;
import souther.compiler.observe.Incompleteness;
import souther.compiler.query.InputCaseEvidence;
import souther.compiler.query.Measure;
import souther.compiler.query.Measurement;
import souther.compiler.query.Weakening;
import souther.compiler.query.WeakeningSet;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.query.OutputCaseEvidence;
import souther.compiler.query.About;
import souther.compiler.query.Adequacy;
import souther.compiler.query.BorderAssessment;
import souther.compiler.query.ItemAssessment;
import souther.compiler.query.Compilation;
import souther.compiler.query.BehaviorEvidence;
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
 * <p>{@code held} is the bar this report is written against, and it is the only thing here that the
 * request decides. How much was measured is not carried: what a measure came to is the measure's own
 * answer, and a report that held the level beside the evidence could read a measure's silence as
 * something other than what the measure said (issue #955). It is an input carried through rather
 * than a value derived from the modules, so filtering the report leaves it alone.
 */
public record AdequacyReport(int schemaVersion, String compilerVersion, Adequacy.AdequacyBar held,
                             WeakeningSet weakenedBy, List<ModuleReport> modules) {

    /**
     * How far the whole measurement got, in the report's own word.
     *
     * <p>Derived and not held. A level with no measure of its own is complete exactly when nothing
     * beneath it went without anything, so a word kept beside the union would be a second thing to
     * keep true — which is what this report used to have at all three levels.
     */
    public MeasurementStatus status() {
        return ReportMeasurement.statusOf(weakenedBy);
    }

    public static final int SCHEMA_VERSION = 7;

    /**
     * Whether the rows meet what the bar this report is read against asks of them.
     *
     * <p>Apart from {@code status}, which says whether the measurement could be made at all. A
     * measurement that came back complete over a model with an arm nothing reaches is a measurement
     * that worked and a model that does not satisfy it, and one word cannot say both.
     */
    public enum AdequacyStatus {
        /** Every measure the bar rests on came to an answer, and none of them found a gap. A model
         *  the bar can ask nothing of is here too: it was asked and had nothing to answer for. */
        SATISFIED,
        /** A measure found a gap the bar refuses over. One is enough, whatever else could not be
         *  measured. */
        NOT_SATISFIED,
        /** A measure that could have found such a gap was not made, or could not be. */
        UNDETERMINED
    }

    public record ModuleReport(String module, SourceId declaredIn,
                               List<BehaviorReport> behaviors,
                               List<Adequacy.Finding> declarations,
                               List<Adequacy.DeclaredDebt> debts) {

        /**
         * What the module is short of that is not any behavior's.
         *
         * <p>A line an {@code invariant} drew is a fact about the type — whether a row standing at
         * the boundary of {@code UserId} is believed is a question about {@code UserId}, and the
         * behaviors carrying it say nothing about the length of a user id (issue #1062). Held in a
         * behavior's list, it had to be filed under whichever of them a walk reached first.
         *
         * <p>Here rather than left out of the report, so that a finding whose subject is not a
         * behavior cannot go missing between the measure and the page.
         */
        public ModuleReport {
            behaviors = List.copyOf(behaviors);
            declarations = List.copyOf(declarations);
            debts = List.copyOf(debts);
        }

        /**
         * Why the measures of this module could not read everything, as the reasons themselves.
         *
         * <p>Derived from what its behaviors went without, and not gathered beside it. These are the
         * lines a document prints under a behavior and the entries a build counts; the status above
         * them is the same union read another way, and the two were assembled separately — one from
         * the measures, one by walking the sources again. A list built the second way can hold a
         * reason no measure carried, which is a report saying something the measures beside it do
         * not (issue #996).
         *
         * <p>One entry per reason. A reason that counts against every behavior is carried by every
         * one of them and is one thing to tell an author, and a module-wide failure found from each
         * of three attached files is one failure.
         */
        public List<Incompleteness> incompleteness() {
            Map<Object, Incompleteness> byIdentity = new LinkedHashMap<>();
            for (Incompleteness gap : weakenedBy().observationCauses()) {
                byIdentity.putIfAbsent(gap.identity(), gap);
            }
            return List.copyOf(byIdentity.values());
        }

        /**
         * What this module went without: the union of its behaviors, and nothing of its own.
         *
         * <p>Derived and not held. What a module could not read reaches it through the measures that
         * lost by it — a source none of whose rows were seen counts against every behavior the
         * module has, and the reading of each of them says so. Read a second time from a list of the
         * module's own, this report was giving a raw fact its meaning as a weakening, which is a
         * measure's answer and not a renderer's (issue #953).
         */
        public WeakeningSet weakenedBy() {
            WeakeningSet out = WeakeningSet.none();
            for (BehaviorReport behavior : behaviors) {
                out = out.union(behavior.weakenedBy());
            }
            return out;
        }

        /** How far this module's measurement got. Derived, for the reason
         *  {@link AdequacyReport#status()} gives. */
        public MeasurementStatus status() {
            return ReportMeasurement.statusOf(weakenedBy());
        }
    }

    /**
     * @param reading   how far the reading of this behavior's rows got, and what it read. The
     *                  counts a document prints are this measurement's value and are absent where
     *                  it has none: a source nobody evaluated leaves no row to count, and printing
     *                  {@code rows 0} for it says the author wrote none (issue #996)
     * @param signature what those rows establish about the cases of its inputs and its output
     * @param claimed   what the body declared cannot arrive, beside the measures rather than in
     *                  them. The two are joined where this report is written and nowhere else,
     *                  which is what keeps a claim from reaching a denominator
     * @param findings  what the measures found and nothing filled, which is what the lines under this
     *                  behavior print and what a build is warned about — one list, read three ways
     */
    public record BehaviorReport(String name, BehaviorImplementation implementation,
                                 BehaviorEvidence evidence,
                                 ClaimAnnotations claimed,
                                 List<Adequacy.Finding> findings) {
        public BehaviorReport {
            findings = List.copyOf(findings);
        }

        /** How far the reading of this behavior's rows got, and what it read. */
        public Adequacy.RowReading reading() {
            return evidence.reading();
        }

        /** What the rows establish about the cases of its inputs and its output. */
        public Adequacy.SignatureEvidence signature() {
            return evidence.signature();
        }

        /** What they establish about the classes and the lines its rules draw. */
        public PartitionEvidence partition() {
            return evidence.partition();
        }

        /** What they establish about the arms of its body. */
        public Adequacy.BranchEvidence branch() {
            return evidence.branch();
        }

        /**
         * What this behavior's measures went without.
         *
         * <p>Derived and not held. It is the union of what its parts went without, which the
         * evidence answers; kept here as well it would be a second thing to keep true, and the
         * report is what used to work it out — over a list of parts written where the document is
         * assembled, which the reading was missing from (issue #996).
         */
        public WeakeningSet weakenedBy() {
            return evidence.weakening();
        }

        /** How far this behavior's measurement got. Derived, for the reason
         *  {@link AdequacyReport#status()} gives. */
        public MeasurementStatus status() {
            return ReportMeasurement.statusOf(weakenedBy());
        }

        /**
         * How many {@code example} rows name this behavior, where its rows were read.
         *
         * <p>Absent where they were not. A count of what came back is not a count of what was
         * written, and a reader shown {@code 0} beside a source nobody evaluated is told the author
         * wrote no row — which sends them to write one that may already be there.
         */
        public java.util.OptionalInt rows() {
            return reading().measured().made()
                    .map(seen -> java.util.OptionalInt.of(seen.rows().size()))
                    .orElseGet(java.util.OptionalInt::empty);
        }

        /** How many of those are recorded rather than evaluated. Absent for the reason
         *  {@link #rows()} is. */
        public java.util.OptionalInt pending() {
            return reading().measured().made()
                    .map(seen -> java.util.OptionalInt.of((int) seen.rows().stream()
                            .filter(r -> r.disposition()
                                    == souther.compiler.observe.Disposition.PENDING)
                            .count()))
                    .orElseGet(java.util.OptionalInt::empty);
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
        WeakeningSet overall = WeakeningSet.none();
        for (String name : compilation.modules()) {
            Prepared module = compilation.module(name);
            if (module == null) {
                continue;   // a module that did not get far enough to have behaviors
            }
            ModuleReport report = moduleReport(compilation, name, module);
            modules.add(report);
            overall = overall.union(report.weakenedBy());
        }
        Adequacy.Asked asked = compilation.db().ask(new Adequacy.Requested()).value();
        Adequacy.AdequacyBar held =
                asked == null ? Adequacy.Asked.NOTHING.held() : asked.held();
        return new AdequacyReport(SCHEMA_VERSION, ModuleMetadata.compilerVersion(),
                held, overall, List.copyOf(modules));
    }

    private static ModuleReport moduleReport(Compilation compilation, String name, Prepared module) {
        // The same reading every measure beside them reads, asked for rather than made again. Two
        // evaluations of one model can disagree — a row that ran out of time under the instrumented
        // one and held under the other — and a report whose counts came from one while its coverage
        // came from the other would say a case is verified and its arm unreached in the same breath.
        // The findings `--strict` exits on come from these same rows, so the exit code and what is
        // printed agree. This walked the sources itself and built the second of those two readings
        // (issue #996).
        //
        // Held to answering, unlike the measures below. A module got this far because its shapes
        // are prepared, which is the one thing the reading needs to answer for every behavior of
        // it — so an absence here is this report and that query disagreeing about what a module is,
        // and there is no reading of it that is not a guess.
        Map<String, Adequacy.RowReading> readings = java.util.Objects.requireNonNull(
                compilation.db().ask(new Adequacy.Rows(name)).value(),
                () -> "the rows of `" + name + "` were not read for or against");
        Map<String, Adequacy.SignatureEvidence> signatures =
                compilation.db().ask(new Adequacy.Witnesses(name)).value();
        Map<String, PartitionEvidence> partitions =
                compilation.db().ask(new Adequacy.Coverage(name)).value();
        Map<String, Adequacy.BranchEvidence> branches =
                compilation.db().ask(new Adequacy.BranchCoverage(name)).value();
        // What each body declared, read where it was judged. Beside the measures and never inside
        // one: this report is where the two are put together.
        Map<String, ClaimAnnotations> claims =
                compilation.db().ask(new souther.compiler.query.Bodies.Claimed(name)).value();
        // The lines this report prints and the warnings a build is given are the same list, asked for
        // once here. A second reading of the evidence would be a second statement of what a gap is.
        List<Adequacy.Finding> findings =
                compilation.db().ask(new Adequacy.Findings(name)).value();
        List<BehaviorReport> behaviors = new ArrayList<>();
        for (Hir.BehaviorDef behavior : module.behaviors()) {
            // Asked of the answer, and not chosen between its states from what the answer did not
            // say. `NOT_ASKED` and `NONE` are both things the reading says — a build that reads no
            // rows, and a reading that finished and found none — so picking one from an absent key
            // is a reader deciding what the producer answered (issue #996).
            Adequacy.RowReading reading = Adequacy.Rows.readingFor(readings, behavior.name());
            // Anything larger than a behavior holds this one: a source that could not be evaluated is
            Adequacy.SignatureEvidence signature =
                    signatures == null ? null : signatures.get(behavior.name());
            // Null where the coverage did not answer at all, which is the compile not having got
            // that far and is not this behavior having nothing to cover. Read and never worked out:
            // a coverage that answered answers for every behavior of the module, so what a key is
            // for is what the measure said about it — this used to reach `NONE` for a composition
            // by asking the declarations again, which is a reader settling what a measure means.
            PartitionEvidence partition = partitions == null ? null
                    : partitions.get(behavior.name());
            // Null where the compile did not get far enough to be asked, which is not a measure that
            // came back with nothing. Every measure that did run says why it has no number.
            Adequacy.BranchEvidence branch =
                    branches == null ? null : branches.get(behavior.name());
            behaviors.add(new BehaviorReport(behavior.name(),
                    module.implementationOf(behavior),
                    new BehaviorEvidence(reading, signature, partition, branch),
                    claims == null ? ClaimAnnotations.NONE
                            : claims.getOrDefault(behavior.name(), ClaimAnnotations.NONE),
                    ofBehavior(findings, behavior.name())));
        }
        List<Adequacy.DeclaredDebt> debts =
                compilation.db().ask(new Adequacy.DeclaredBorders(name)).value();
        return new ModuleReport(name, compilation.sourceIdOf(name), behaviors,
                findings == null ? List.of()
                        : findings.stream()
                                .filter(each -> !(each.subject()
                                        instanceof souther.compiler.query.FindingSubject.OfABehavior))
                                .toList(),
                debts == null ? List.of() : debts);
    }

    /**
     * The declarations' findings that one of {@code shown} carries.
     *
     * <p>Asked of the debt, which knows which behaviors read the line. A line no behavior in this
     * report carries is work nobody reading it can do, and one that some behavior here carries is
     * work a row written in front of the reader settles.
     */
    private static List<Adequacy.Finding> carriedBy(List<Adequacy.Finding> declarations,
                                                    List<BehaviorReport> shown) {
        java.util.Set<String> names = shown.stream().map(BehaviorReport::name)
                .collect(java.util.stream.Collectors.toCollection(java.util.LinkedHashSet::new));
        return declarations.stream()
                .filter(each -> !(each.about()
                        instanceof About.APointOfADeclaredBorder(var debt))
                        || names.stream().anyMatch(debt::carriedBy))
                .toList();
    }

    /** The findings about one behavior. Grouped here, where a block per behavior is printed, and
     *  not by the measure: what each finding is about is its own answer. */
    private static List<Adequacy.Finding> ofBehavior(List<Adequacy.Finding> findings, String name) {
        return findings == null ? List.of()
                : findings.stream().filter(each -> each.subject().isBehavior(name)).toList();
    }

    /**
     * What the module's declarations are short of, under the declaration that wrote the rule.
     *
     * <p>Under the declaration and not under a behavior, because that is where an author fixes it. A
     * line an {@code invariant} drew is a fact about the type — whether a row standing at the
     * boundary of {@code UserId} is believed is a question about {@code UserId} — and it is met by a
     * row written anywhere the type is carried. Printed under a behavior, it would have to be
     * printed under whichever one a walk reached first, and an author sent there would be sent to a
     * body that says nothing about the length of a user id (issue #1062).
     *
     * <p>The two points against the line and no others. What a row well inside the border shows is
     * about the region of one position, so it stays with that position's behavior — which is why
     * this block holds one kind of line and the block above still holds both.
     *
     * <p>After the behaviors, so that a reader who has just read what each body is short of reads
     * what the model itself is short of once.
     */
    private void declared(StringBuilder out, ModuleReport module, SourceNameResolver names) {
        Map<String, List<Adequacy.Finding>> byDeclaration = new java.util.LinkedHashMap<>();
        for (Adequacy.Finding each : module.declarations()) {
            byDeclaration.computeIfAbsent(each.named(), _ -> new ArrayList<>()).add(each);
        }
        byDeclaration.forEach((declaration, findings) -> {
            out.append(String.format("  %s%n", declaration));
            for (Adequacy.Finding f : findings) {
                if (f.about() instanceof About.APointOfADeclaredBorder(var debt)) {
                    // What the point asks, in its own words. A point against the line names a value
                    // and a point beside it names a run, and a sentence that wrote `=` for both said
                    // a run was one value.
                    out.append(String.format("      %s no row is at the %s point %s (%s)%n",
                            mark(f), debt.role(), debt.said(), debt.id().named()));
                }
            }
        });
    }

    /** This report with only the modules and behaviors the caller asked about. A name that matches
     * nothing leaves an empty report rather than the whole one. */
    public AdequacyReport only(String module, String behavior) {
        List<ModuleReport> kept = new ArrayList<>();
        WeakeningSet overall = WeakeningSet.none();
        for (ModuleReport m : modules) {
            if (module != null && !module.equals(m.module())) {
                continue;
            }
            List<BehaviorReport> behaviors = behavior == null ? m.behaviors()
                    : m.behaviors().stream().filter(b -> behavior.equals(b.name())).toList();
            // What a filtered report says is about what it shows, and nothing here arranges that.
            // The reasons are what the behaviors shown went without, so dropping a behavior drops
            // what only it carried and keeps what a whole source cost every one of them. That was a
            // filter over a list of the module's own, which is a second statement of who a reason
            // counts against — asked of the reason where it belongs (issue #996).
            // What the module's declarations are short of, kept where a behavior that is shown
            // carries the line. A line an `invariant` drew is not any behavior's, and it is
            // discharged by a row written for any behavior carrying the type — so it is work the
            // reader of this report can do, and a verdict that kept a line none of the behaviors
            // shown carries would be a verdict about what the reader cannot see.
            // And the debts those behaviors carry, for the same reason and by the same question:
            // a verdict about a line none of them carries is a verdict about what the reader
            // cannot see.
            java.util.Set<String> names = behaviors.stream().map(BehaviorReport::name)
                    .collect(java.util.stream.Collectors.toCollection(java.util.LinkedHashSet::new));
            ModuleReport one = new ModuleReport(m.module(), m.declaredIn(), behaviors,
                    carriedBy(m.declarations(), behaviors),
                    m.debts().stream()
                            .filter(owed -> names.stream().anyMatch(owed.debt()::carriedBy))
                            .toList());
            kept.add(one);
            overall = overall.union(one.weakenedBy());
        }
        return new AdequacyReport(schemaVersion, compilerVersion, held, overall,
                List.copyOf(kept));
    }

    /** How many rows are recorded and waiting for a {@code let}, across everything reported.
     *
     * <p>Reported and never gated on. Waiting is the normal state of a model being written, and a
     * build that refused one would refuse the practice of recording what an injected behavior owes. */
    public int pendingRows() {
        return modules.stream().flatMap(m -> m.behaviors().stream())
                .map(BehaviorReport::pending)
                .filter(java.util.OptionalInt::isPresent)
                .mapToInt(java.util.OptionalInt::getAsInt).sum();
    }

    /**
     * Everything the measures found, across everything reported.
     *
     * <p>What the declarations are short of as well as what the bodies are. A line an
     * {@code invariant} drew is not any behavior's, and a walk over the behaviors alone left it out
     * of the verdict — so a report printed a gap and said the rows met the bar under it
     * (issue #1062).
     */
    public List<Adequacy.Finding> findings() {
        return java.util.stream.Stream.concat(
                        modules.stream().flatMap(m -> m.behaviors().stream())
                                .flatMap(b -> b.findings().stream()),
                        modules.stream().flatMap(m -> m.declarations().stream()))
                .toList();
    }

    /** The findings a build is entitled to refuse: a measure came to an answer and the answer was
     *  that something the rows are asked for is not there. */
    public List<Adequacy.Finding> adequacyGaps() {
        return findings().stream().filter(f -> f.isAdequacyGap(held)).toList();
    }

    /**
     * Whether the rows meet what the bar this report is read against asks of them.
     *
     * <p>Derived on every call rather than held, because {@link #only(String, String)} makes a report
     * of part of this one and a verdict about the whole would be a verdict about behaviors that report
     * does not show.
     *
     * <p>A gap is answered before anything about how much was measured: one is enough, whatever else
     * could not be measured, which is what {@link AdequacyStatus#NOT_SATISFIED} says it means.
     *
     * <p>No measure to be short of is not a doubt. A model the bar can refuse nothing about — every
     * measure it reads inapplicable — has been asked what the bar asks and has nothing to answer
     * for, so it is satisfied rather than undetermined; {@code undetermined} is for a measure that
     * could have found a gap and was not made. Answered the other way, this reported a doubt nobody
     * could act on and no row could settle, and it was doing it on the strength of a list that had
     * dropped exactly the measures nobody was going to make (issue #955).
     */
    public AdequacyStatus adequacy() {
        if (!adequacyGaps().isEmpty()) {
            return AdequacyStatus.NOT_SATISFIED;
        }
        // Every measure the verdict rests on came to an answer nothing weakened. A measurement made
        // in part is one whose gaps may not be gaps, and one that could not be finished came to no
        // answer at all — neither settles a bar.
        //
        // The support evidence and the domain measures, which are two questions. This used to ask
        // the second and then reach past it for a list of reasons, which is the bar's decision
        // taken away from it: a reason about a measure this build is not held to held the verdict
        // open, and a reason no measure carried held it open on nobody's authority (issue #996).
        return java.util.stream.Stream.concat(requiredSupport().stream(),
                        requiredEvidence().stream())
                .allMatch(m -> m instanceof Measurement.Complete<?>)
                ? AdequacyStatus.SATISFIED : AdequacyStatus.UNDETERMINED;
    }

    /**
     * What the verdict rests on that is not a measure of the model: the reading of the rows.
     *
     * <p>Every domain measure below is counted over the rows, so how far they were read is what
     * each of those answers is worth. A measure of the model that found no gap over rows that did
     * not all come back has found that no gap is <em>visible</em>, which is not the same answer and
     * is the one a bar cannot be settled by.
     *
     * <p>Required whether or not any domain measure applies, which is where the two differ. "No
     * measure to be short of is not a doubt" is about the model: a behavior the bar can refuse
     * nothing about has been asked and has nothing to answer for (issue #955). Its rows were still
     * read or not read, and that is a separate fact — a module every measure of which is
     * inapplicable and whose one row did not come back is undetermined, and every one of those
     * measures is entitled to say it went without nothing (issue #996).
     *
     * <p><b>Except where the build does not read rows at all.</b> That is not a reading that fell
     * short; it is this build saying it makes no measurement over rows, and every measure over them
     * says so too — so a bar that asks for one of those is held open by that measure, and a bar
     * that asks for none of them is a bar this build was never going to answer. Held open here as
     * well, a build that measures nothing would be undetermined about a model the bar can refuse
     * nothing about, which is the answer #955 took out.
     */
    private List<Measurement<?>> requiredSupport() {
        List<Measurement<?>> support = new ArrayList<>();
        for (ModuleReport module : modules) {
            for (BehaviorReport behavior : module.behaviors()) {
                Measurement<?> reading = behavior.reading().measured();
                if (!(reading instanceof Measurement.NotMeasured<?>)) {
                    support.add(reading);
                }
            }
        }
        return support;
    }

    /**
     * The measures of the model this verdict rests on: the ones that could find a gap the bar
     * refuses over.
     *
     * <p>Two questions and each asked of the one thing that answers it. Whether a measure was made,
     * and how much of it, is the measurement's own answer and is read from it. Which kinds of gap a
     * verdict needs an answer about is the bar's, and is read from that — so a measure that finds
     * only what this build is not held to cannot leave the verdict undetermined for want of an
     * answer, and a measure it is held to cannot be left out.
     *
     * <p>Which is why each entry below names the kind it can find. Read as "everything that was
     * measured", a build held to a bar that asks nothing of the classes was undetermined for a
     * position nobody had classified, and a build that asked for the classes was satisfied while
     * one went unread.
     *
     * <p>Whether a measure applies at all is the measure's own answer, and never the shape of what
     * came back. A behavior with no body has no arms, and a position whose rules the walk never
     * reached leaves no boundary behind — in both cases the numbers look exactly like a measure
     * that was made and found nothing, so a report reading them back would call the first adequate
     * and the second covered.
     */
    private List<Measure<?>> requiredEvidence() {
        List<Measure<?>> measures = new ArrayList<>();
        for (ModuleReport module : modules) {
            for (BehaviorReport behavior : module.behaviors()) {
                // The cases of the signature, which every bar refuses over.
                if (behavior.signature() != null
                        && refusesAny(Adequacy.Kind.OUTPUT_CASE_UNSPECIFIED,
                                Adequacy.Kind.INPUT_CASE_UNSPECIFIED)) {
                    add(measures, behavior.signature().counted());
                }
                if (behavior.branch() != null && refusesAny(Adequacy.Kind.ARM_UNREACHED)) {
                    add(measures, behavior.branch().measured());
                }
                if (behavior.partition() == null) {
                    continue;
                }
                // The measure answers for itself, and its entries answer for themselves. Read off
                // the entries alone, a measure that derived nothing contributed nothing and a
                // behavior whose every bound sits one type away from the position it takes came out
                // adequate on the strength of a measurement nobody made.
                //
                // The derivation of the lines, and not the derivation of the positions. A position
                // with a bound and no division — an `Int` a rule floors and nothing cuts — is an
                // ordinary shape whose boundary measure is made in full, and holding the verdict
                // open for it would say a model was unmeasured on the strength of the one measure
                // that was.
                if (refusesAny(Adequacy.Kind.BOUNDARY_UNMET,
                        Adequacy.Kind.DOMAIN_POINT_UNCOVERED)) {
                    add(measures, behavior.partition().bounded());
                }
                // What the rows reach of each position, which finds a class no row is in — a gap
                // the `classes` bar refuses over and no other does. A bar that asks nothing about
                // the classes is not held open by one nobody read, and is not satisfied by one that
                // was.
                //
                // The derivation as well as the positions it produced, the way the lines are asked
                // for above. Which positions there are to cover is the first half of the answer: a
                // reading that did not run out produced the axes it reached and no others, so
                // walking those alone leaves a position nobody could derive looking exactly like a
                // position with nothing to cover — and a bar that refuses over a class no row is in
                // was satisfied by the classes nobody had found yet. A behavior the reading proved
                // divides nothing answers {@code NotApplicable} and is dropped below, so this holds
                // nothing open that was never going to be measured.
                if (refusesAny(Adequacy.Kind.AXIS_CLASS_UNCOVERED)) {
                    add(measures, behavior.partition().partitioned());
                    behavior.partition().axes().forEach(axis -> add(measures, axis.reached()));
                }
                // And of a border's four points, the ones the bar asks for — of the lines this
                // behavior is owed. A line a declaration is owed is answered once for the module
                // below, from every reading of it: read here as well, a row standing at it in one
                // behavior would be weighed against another behavior having no rows, and the
                // verdict would hold open what the aggregation had settled (issue #1062).
                // One measurement per thing the reading is owed a row for, since each of them is an
                // obligation: a place two of this body's rules drew a line at leaves a run owed to
                // each, and a verdict counting the role once would be short by the rest. How many
                // rows answer them is a different count and is the generator's.
                BorderAssessment.pointsOf(behavior.partition().boundaries()).stream()
                        .filter(p -> held.requires(p.role()))
                        .forEach(p -> p.owedHere()
                                .forEach(_ -> add(measures, measurementOf(p.item()))));
                // Which of the four those are is the bar's answer and not a second reading of it
                // here: a build refusing over a missing IN row and calling a model satisfied while
                // the IN point could not be measured would be held to one bar in one place and
                // another in the other. What the report says about itself still reads all four:
                // how much of the measurement was made and what a build is held to are two
                // questions.
                // A dropped axis is not asked after here. What it was carrying went with it and no
                // question stands for it, which is a fact about the measure's reading — so it
                // leaves the measure's own answer short of complete, and reading it back off the
                // list of what was dropped would be this report deciding a measure's status again.
            }
            // And what the module's declarations are owed, once each and from every reading.
            //
            // The debts and not their findings. A line a row already stands at has no finding, so a
            // denominator made of the findings is a denominator made of the gaps — which is
            // satisfied by whatever it does not contain.
            for (Adequacy.DeclaredDebt owed : module.debts()) {
                if (held.requires(owed.debt().role())) {
                    add(measures, measurementOf(owed.debt().item()));
                }
            }
        }
        return measures;
    }

    /** Whether the bar refuses over any of {@code kinds}, which is what puts the measure that finds
     *  them among the answers a verdict needs. */
    private boolean refusesAny(Adequacy.Kind... kinds) {
        for (Adequacy.Kind kind : kinds) {
            if (held.refuses(kind)) {
                return true;
            }
        }
        return false;
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
    private void add(List<Measure<?>> measures, Measure<?> measure) {
        if (measure != null && !(measure instanceof Measure.NotApplicable<?>)) {
            measures.add(measure);
        }
    }

    /** One border point's own measurement, asked of the point. Written out here as well, the answer
     *  a point nobody is owed a row at gets would be this report deciding it. */
    private static Measure<?> measurementOf(ItemAssessment item) {
        return item.weakeningSource();
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
        Map<BehaviorImplementation, Integer> counted = new java.util.EnumMap<>(BehaviorImplementation.class);
        for (BehaviorImplementation each : BehaviorImplementation.values()) {
            counted.put(each, 0);
        }
        for (ModuleReport module : modules) {
            out.append(String.format("%s measurement: %s%n",
                    DisplayColumns.padRight(module.module(), 56),
                    wire(ReportMeasurement.statusOf(module.weakenedBy()))));
            for (BehaviorReport behavior : module.behaviors()) {
                counted.merge(behavior.implementation(), 1, Integer::sum);
                // A number where the rows were read, and what stopped them being read where they
                // were not. Written as `0` for both, this line said an author had written no row
                // for a behavior whose rows nobody had looked at.
                out.append(String.format("  %s %s %s%n",
                        DisplayColumns.padRight(behavior.name(), 24),
                        DisplayColumns.padRight(behavior.implementation().written(), 13),
                        behavior.rows().isPresent()
                                ? String.format("rows %-4d pending %d",
                                        behavior.rows().getAsInt(), behavior.pending().getAsInt())
                                : "rows not read"));
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
            declared(out, module, names);
            said(out, module.incompleteness().stream()
                    .filter(gap -> gap.behavior().isEmpty()).toList(), names);
        }
        int total = counted.values().stream().mapToInt(Integer::intValue).sum();
        out.append(String.format("%n%d %s: %d implemented, %d unimplemented, %d injected;"
                        + " %d %s waiting for a `let`.%n",
                total, total == 1 ? "behavior" : "behaviors",
                counted.get(BehaviorImplementation.IMPLEMENTED),
                counted.get(BehaviorImplementation.UNIMPLEMENTED),
                counted.get(BehaviorImplementation.INJECTION_TARGET),
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
    private void said(StringBuilder out, List<Incompleteness> gaps,
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
    private void signature(StringBuilder out, BehaviorReport behavior) {
        Adequacy.SignatureEvidence signature = behavior.signature();
        if (signature == null) {
            return;
        }
        ReportMeasurement<Adequacy.SignatureEvidence.Counted> counted =
                ReportMeasurement.of(signature.counted());
        if (!counted.counted()) {
            // A measure with no number says why, the way the arms do. Leaving the line out instead
            // put two behaviors side by side in one report, one measured on four lines and one on
            // three, with nothing saying the fourth did not apply — and hid the fact worth reading,
            // which is that a behavior answering a bare primitive gets less scrutiny than one
            // answering a sum.
            // A measure nobody asked for is not said at all, the way the arms are not: what was
            // asked for is an input to the whole run, and a line repeating it against every
            // behavior says one fact as many times as the module has behaviors.
            String why = switch (counted.reason()) {
                case Adequacy.SignatureEvidence.NotASum _ ->
                        "not applicable (this behavior's output is not a sum)";
                case Adequacy.SignatureEvidence.NoRows _ ->
                        "not measured (no row names this behavior)";
                // What was read of the declaration is not said here. Which name resolved to nothing
                // is reported where it was written, on the line the author edits.
                case souther.compiler.query.BoundaryForMeasurement.NotDerived _ ->
                        "not measured (this behavior's signature could not be read)";
                case souther.compiler.query.NothingWasAsked _ -> null;
                // Not a word for whatever is left. This measure carries one of the four reason
                // types above and nothing else, so a fifth arriving here is a reason nobody decided
                // a word for — and given the word of one of the others it would be printed as a
                // state it is not. A word standing in for every reason added after it was written
                // is the same defect as a key standing in for every way a measure can have no
                // answer, one surface further out.
                //
                // A throw and not exhaustiveness the compiler checks. What is switched on is a
                // `MeasureReason`, which is a plain interface because two of the reasons here
                // belong to no measure in particular — nobody asked is one fact about the run, and
                // a boundary that could not be worked out is one fact about the behavior, each
                // read by several measures. Sealing a reason type per measure would make those
                // name every measure that reads them, which is the dependency the other way round.
                // Worth revisiting only if the reasons stop being shared.
                default -> throw new IllegalStateException(
                        "the signature measure has no word for " + counted.reason());
            };
            if (why != null) {
                out.append(String.format("    signature   %s%n", why));
            }
            return;
        }
        boolean decided = counted.inFull();
        OutputCaseEvidence output = signature.output();
        if (!output.declared().isEmpty() && output.cases().made().isPresent()) {
            OutputCaseEvidence.Cases cases = output.cases().made().orElseThrow();
            out.append(String.format("    signature   out specified %d/%d  observed %d/%d "
                            + " verified %d/%d%s%n",
                    cases.specified().size(), output.declared().size(),
                    cases.observed().size(), output.declared().size(),
                    cases.verified().size(), output.declared().size(),
                    decided ? "" : "   (partial)"));
            for (Adequacy.Finding f : behavior.findings()) {
                if (f.about() instanceof About.ACaseNoRowExpects(var missing)) {
                    out.append(String.format("      %s %sexpects `%s`%n",
                            mark(f), noRow(f), missing.name()));
                }
            }
            for (Adequacy.Finding f : behavior.findings()) {
                if (f.about() instanceof About.ACaseNothingWasSeenToProduce(var missing)) {
                    out.append(String.format("      %s %sconfirms `%s`%n",
                            mark(f), noRow(f), missing.name()));
                }
            }
        }
        // The positions where the measure counted them. This section is reached only where the
        // signature measure has a number, and a measure with one has read the boundary its
        // positions come off — so there is nothing here that a measure short of one would print,
        // and nothing to stand in for it either.
        for (InputCaseEvidence input : signature.positions()) {
            // Under the same condition as the output line above it, which is the whole of why it is
            // spelled here. It asked its measurement for a number and took a nought where there was
            // none, so an input nobody measured printed `specified 0/3` — a measurement, made by
            // this line rather than by anything that read a row (issue #997). Nothing in this suite
            // reaches it: a behavior no row names and a level that asks for nothing leave the whole
            // signature measure without a number, and this section returns above. Which is a reason
            // to write the condition and not a reason to leave it out — the one thing the two lines
            // must not do is differ.
            if (input.declared().isEmpty() || input.cases().made().isEmpty()) {
                continue;
            }
            // Counted against the cases a row can be written at. A case the body answers `unreachable`
            // for is one the compiler refuses a row for, so leaving it in the denominator would ask
            // for work that cannot be done and hold the model one case short for ever.
            out.append(String.format("                in #%d specified %d/%d%s%n", input.at() + 1,
                    input.cases().made().orElseThrow().specified().size(),
                    input.coverable().size(),
                    input.excluded().isEmpty() ? ""
                            : "   excluded " + input.excluded().size()));
            for (Adequacy.Finding f : behavior.findings()) {
                // Told apart by the input the finding is about rather than by a number written
                // beside it: which one it is, is the evidence's own answer on both sides.
                if (f.about() instanceof About.ACaseNoRowAppliesItTo(var at, var missing)
                        && at.at() == input.at()) {
                    out.append(String.format("      %s %suses `%s`%n",
                            mark(f), noRow(f), missing.name()));
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
    private String mark(Adequacy.Finding finding) {
        return finding.isAdequacyGap(held) ? "!" : "·";
    }

    /**
     * How a finding names what nothing did, given how far its measure got.
     *
     * <p>Where some rows could not be read, a case nothing here claims is a case nothing *seen*
     * claims. The summary already says partial; each line has to say it too, or the lines read as the
     * finding and the word in the margin as a footnote.
     */
    private String noRow(Adequacy.Finding finding) {
        return finding.weakenedBy().isEmpty()
                ? "no row " : "undecided whether a row ";
    }

    /** The positions this report has an axis for, which is what tells a claim it can print beside
     *  one from a claim it has to name a position for. */
    private List<String> measuredPaths(PartitionEvidence partition) {
        return partition.axes().stream().map(PartitionEvidence.AxisCoverage::path).toList();
    }

    /** The model's own words for a claim, where there is one to print. */
    private String because(List<String> reasons) {
        return reasons.size() == 1 ? ": " + reasons.get(0)
                : reasons.isEmpty() ? "" : " on every path";
    }

    /** What a reader is told about a claim nothing settled, in this report's own words. */
    private String unproven(ClaimAnnotations.Why why) {
        return switch (why) {
            case A_RULE_WENT_UNREAD -> "a rule about this position went unread";
            case THE_RULES_LEAVE_THE_POSITION_NOTHING ->
                    "the rules leave this position no value at all";
            case NOTHING_WAS_READ_ABOUT_THE_CASE -> "nothing was read about this case";
            case THE_FORK_IS_NOT_KNOWN_TO_BE_REACHED ->
                    "this arm is inside another, and what reaches it is not read here";
            case THE_ALTERNATIVES_WERE_NOT_KEPT_APART ->
                    "every rule here was read, and what they leave this position together is not"
                            + " what is held of it";
        };
    }

    /**
     * How much of what the model distinguishes the rows reach.
     *
     * <p>A boundary a guard drew is printed as not measured rather than as missed. Meeting it takes
     * more than writing the value — the comparison has to have run — and nothing counts that yet.
     */
    private void partition(StringBuilder out, BehaviorReport behavior,
                                  SourceId declaredIn, SourceNameResolver names) {
        // Whether there is a section at all is settled once, for every surface, and asked of the
        // measurement rather than of the entries beside it. Asked of the entries, a behavior whose
        // measures both had something to say and whose lists happened to be empty was left out of
        // the page while the document wrote what they said (issue #1079).
        if (!(PartitionSection.of(behavior.partition())
                instanceof PartitionSection.Present(PartitionEvidence partition))) {
            return;
        }
        ReportMeasurement<List<PartitionEvidence.AxisCoverage>> partitioned =
                ReportMeasurement.of(partition.partitioned());
        if (!partitioned.counted()) {
            // A measure with no number says why, rather than showing a nought that reads as a
            // measurement. `axes 0   single-axis 0/0` was the same three characters a behavior gets
            // when every position it has was measured and every class covered.
            out.append(String.format("    partition   %s%n",
                    whyNoPartition(partitioned.reason())));
        } else {
            // Counted over the positions that were measured. A position nothing was measured at
            // contributes no classes to the denominator: nought out of two reads as two gaps, and a
            // measure that was never made found none.
            List<PartitionEvidence.AxisCoverage> measuredAxes = partition.axes().stream()
                    .filter(a -> a.reached().made().isPresent()).toList();
            int classes = measuredAxes.stream().mapToInt(a -> a.classes().size()).sum();
            int covered = measuredAxes.stream()
                    .mapToInt(a -> a.reached().made().orElseThrow().covered().size()).sum();
            // Over the positions this line counts and no others. A claim about a position no axis
            // was derived at is said further down, under its own name — counted here it would be a
            // number taken out of a denominator that never held it.
            int excluded = (int) measuredAxes.stream()
                    .flatMap(each -> behavior.claimed().at(each.path()).stream())
                    .filter(ClaimAnnotations.Said::settled).count();
            out.append(String.format("    partition   axes %d   equivalence partitions %d/%d%s%s%s%n",
                    partition.axes().size(), covered, classes,
                    excluded == 0 ? "" : "   excluded " + excluded,
                    notes(partition.axes(), a -> a.reached().made().isEmpty(),
                            a -> whyNoAxis(ReportMeasurement.of(a.reached()).reason())),
                    inFull(partitioned.status())));
            // The position as well as the class. A class name alone is the same words about two
            // positions of one behavior whose types divide into classes named after the same cases,
            // and a reader told one of them cannot say which position to write the row at. Which
            // name a position goes by is settled here and not by the class: the two the axis holds
            // are for different readers, and this one writes the term a row is written against.
            for (Adequacy.Finding f : behavior.findings()) {
                if (f.about() instanceof About.AClassNoRowIsIn(var missing)) {
                    out.append(String.format("      %s %s `%s` at %s%n", mark(f),
                            f.weakenedBy().isEmpty()
                                    ? "no row is in" : "undecided whether a row is in",
                            missing.name(), missing.axis().path()));
                }
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
        undivided(out, behavior, names, declaredIn);
        // On a line of its own, and this is the whole of why it has one. Counting combinations
        // across two positions is the neighbouring technique rather than this one, and printed at
        // the end of the partition line it sat beside the border counts where a reader could add
        // them up into a total neither of them is part of.
        //
        // Under the same condition as before and not a new one: these counts used to be the tail of
        // the partition line, which is written in the arm this tests for. Moving them out of that
        // arm is what makes the condition something to spell rather than something to inherit.
        if (partitioned.counted()) {
            String combinations = combinations(partition.pairs());
            if (!combinations.isEmpty()) {
                out.append(String.format("    combination %s%n", combinations));
            }
        }
        // Counted where both questions have an answer: the line was measured against the rows, and
        // something has shown a row can be written at it. The two are separate observations and are
        // filtered separately — a line nobody measured and a line nothing promises are not the same
        // absence, and printing them under one sentence said "not known to be writable" about
        // behaviors whose only problem was that nobody had written a row yet.
        // Counted over the coverage items and named as such. A border owes a row at up to four
        // points, so a count of borders would say a border with one point met and three missed was
        // as covered as one with nothing to owe but that point — and how many items a border owes is
        // the rule's answer rather than a constant.
        List<BorderAssessment.Point> points =
                BorderAssessment.pointsOf(partition.boundaries()).stream()
                        .filter(p -> p.item() instanceof ItemAssessment.Owed).toList();
        List<BorderAssessment.Point> measured = points.stream()
                .filter(p -> owed(p).coverage().made().isPresent())
                .filter(p -> owed(p).writabilityEvidence().known()).toList();
        List<BorderAssessment.Point> unpromised = points.stream()
                .filter(p -> !owed(p).writabilityEvidence().known()).toList();
        long met = measured.stream().filter(p -> owed(p).hasRowWitness()).count();
        // A point read from rows some of which could not be read. What was not found there is
        // undecided rather than absent, which is the measurement's answer and no longer a third
        // case of the verdict beside it.
        long undecided = measured.stream()
                .filter(p -> owed(p).coverage() instanceof Measurement.Partial<?>)
                .count();
        // The points the model's own rules discharged. Said rather than left out of the numbers: a
        // reader working to a coverage criterion counts four items per border, and a border showing
        // two of them with nothing beside it reads as this compiler being short of the other two.
        long excluded = partition.boundaries().stream()
                .mapToLong(b -> b.excluded().size()).sum();
        ReportMeasurement<List<BorderAssessment>> bounded =
                ReportMeasurement.of(partition.bounded());
        if (!bounded.counted()) {
            // `0/0` said the rows were at every line there was. What it meant was that nobody found
            // a line to be at, which a model whose bounds sit one type away from the position the
            // behavior takes has, and which is the shape of every behavior that validates raw input.
            out.append(String.format("    border      %s%n",
                    whyNoBoundary(bounded.reason())));
        } else {
            out.append(String.format("    border      borders %d   coverage items %d/%d%s%s%s%s%n",
                    partition.boundaries().size(), met, measured.size(),
                    excluded == 0 ? "" : "   excluded " + excluded,
                    notes(points,
                            p -> owed(p).coverage().made().isEmpty(),
                            p -> whyNoBoundaryItem(owed(p).coverage())),
                    undecided == 0 ? "" : "   (" + undecided + " undecided: a value was not read)",
                    inFull(bounded.status())));
        }
        // A border the model drew that nothing here answered for, said whether or not one came of
        // it. It is exactly where none did that the question stands, so this cannot be written by
        // walking the borders.
        unaccounted(out, behavior, names, declaredIn,
                question -> !aboutTheClasses(question));
        // The rule as this report writes it. The finding carries the rule and not words about it,
        // because what to say differs between here — where a file has a name — and the warning built
        // from the same finding, where nothing knows what to call one.
        //
        // The two kinds are printed alike and refuse differently. A row against the line is a gap a
        // build can be told to refuse over and a row away from it is not, which is a decision about
        // what a build is held to and not about what a reader is shown — printed apart, the second
        // would read as a lesser finding rather than as the second half of one technique.
        // The points against the line first and the ones away from it after, which is why this is
        // two passes over one list rather than one: the measure finds a border's four items
        // together, and printed in that order the two halves would be interleaved.
        for (boolean againstTheLine : List.of(true, false)) {
            for (Adequacy.Finding f : behavior.findings()) {
                if (f.about() instanceof About.APointOfABorder(var point, var _)
                        && point.role().againstTheLine() == againstTheLine) {
                    // `the` for a point and `an` for a run. Two of the four are one value and the
                    // other two are met anywhere in a run of them, so a reader told there is no row
                    // at `the IN point` is being sent after a value that does not exist.
                    out.append(againstTheLine
                            ? String.format("      %s no row is at the %s point %s = %s (%s)%n",
                                    mark(f), point.role(), point.border().axis(),
                                    point.against(), point.border().describe(names, declaredIn))
                            : String.format("      %s no row is at an %s point of %s, %s (%s)%n",
                                    mark(f), point.role(), point.border().axis(),
                                    point.against(), point.border().describe(names, declaredIn)));
                }
            }
        }
        // Said and not counted. Nothing has shown a row can be written at these — the projection
        // could not read every rule of the value, and nothing built one either — so they are not
        // rows anybody is owed, and they are still the only thing there is to say about the
        // position.
        for (BorderAssessment.Point p : unpromised) {
            // What the search came to, beside the verdict it did not decide. Whether this point is
            // counted turns on whether a concrete value was accepted at it, so a reader looking at
            // two models that differ here is looking at what the compiler could establish — and
            // without this line the difference reads as the tool being arbitrary.
            out.append(String.format("      · not known to be writable: the %s point %s %s (%s)%s%n",
                    p.role(), p.border().axis(), p.asked(),
                    p.border().describe(names, declaredIn),
                    whatWasTried(owed(p).attempt(), names, declaredIn)));
        }
        // And what the model itself answered, which is not a row anybody is behind on. Named by the
        // reason rather than left blank: a point the rules refuse and a point this language cannot
        // write down are counted out for opposite reasons, and a reader acts on them differently.
        for (BorderAssessment.Point p : BorderAssessment.pointsOf(partition.boundaries())) {
            if (p.item() instanceof ItemAssessment.NotOwed not) {
                out.append(String.format("      · no %s point is owed at %s (%s): %s%n",
                        p.role(), p.border().label(), p.border().describe(names, declaredIn),
                        whyNotOwed(not.reason())));
            }
        }
    }

    /** The owed half of a point this report has already filtered to the owed ones. */
    private ItemAssessment.Owed owed(BorderAssessment.Point point) {
        return (ItemAssessment.Owed) point.item();
    }

    /** What settled a point nobody is owed a row at, in the words the report promises its reader. */
    private String whyNotOwed(souther.compiler.partition.NotOwedReason reason) {
        return switch (reason) {
            case THE_RULES_REFUSE_IT -> "excluded — the rules leave no value there";
            case THE_CARRIER_NAMES_NO_NEIGHBOUR ->
                    "this order names no value there, so the point cannot be written";
            case THE_RULE_NAMES_A_VALUE_NOT_A_SIDE ->
                    "the rule names a value rather than a side, so neither neighbour is the nearer";
        };
    }

    /**
     * What the classes measure could not say, said under the classes measure.
     *
     * <p>Under the line these are about, which is the partition and not the boundary. A comparison
     * between two positions divides neither of them and draws a line all the same, so the note saying
     * the position went undivided sat two rows under a boundary count that was counting the line that
     * very comparison drew — one measure's silence printed as though it were the other's.
     */
    private void undivided(StringBuilder out, BehaviorReport behavior,
                                  SourceNameResolver names, SourceId declaredIn) {
        for (Adequacy.Finding f : behavior.findings()) {
            if (f.about() instanceof About.APositionNoLineDivides(var position)) {
                out.append(String.format("      %s not derivable: %s%n", mark(f), position.at()));
            }
        }
        // Said apart from the line above it, which is the whole of what this pair is for: one names
        // a position the model divides no way, and this one a rule nobody could turn into a line.
        //
        // Named by the rule, as the accounting's line is. A position was all a reader used to be
        // given, which sent them looking for a rule the sentence never named — and two rules
        // stopped by one limit at one position came out as one line.
        for (Adequacy.Finding f : behavior.findings()) {
            if (f.about() instanceof About.ARuleWithoutALine(var it)) {
                // Two sentences, because two opposite things are being said. A form no reader takes
                // apart is a limit of this compiler; a rule whose quantity is empty was read from
                // end to end and says what it says. Written under one word, a line read "not read:
                // it was read to the end and cuts nothing" — which is what the reader is left to
                // make sense of.
                out.append(String.format("      %s %s: %s — %s, about `%s`%n",
                        mark(f), it.readingStopped() ? "not read" : "no line",
                        cited(it.cited(), names, declaredIn),
                        whyUnread(it.reason()), it.at()));
            }
        }
        // And a position whose rules this reading never arrived at, which names no rule because
        // nothing observed one. Its own line, so that a reader is not left reading an absent rule
        // to work out which of the two they are being told.
        for (Adequacy.Finding f : behavior.findings()) {
            if (f.about() instanceof About.APositionThisCouldNotRead(var it)) {
                out.append(String.format("      %s not read: %s (%s)%n",
                        mark(f), it.at(), whyUnread(it.reason())));
            }
        }
        // And a third thing, said apart from both: a rule written about a position the axes did
        // measure that nothing took in. The classes beside it are what the model was read to say,
        // and this rule may yet refuse one of them — which is a different thing to act on from a
        // position nothing established anything about. Named by the rule, since a position is not
        // what an author edits.
        for (Adequacy.Finding f : behavior.findings()) {
            if (f.about() instanceof About.APositionWhoseRulesWereNotReached(var axis)) {
                out.append(String.format("      %s rules not reached: %s%n",
                        mark(f), axis.path()));
            }
        }
        // The questions this measure answers: which values may stand where, which classes hold
        // them, and which value a rule tells from every other. A border is the section below's.
        unaccounted(out, behavior, names, declaredIn, AdequacyReport::aboutTheClasses);
    }

    /**
     * What stopped a derivation, in the words this document promises its reader.
     *
     * <p>Here and not where the position was found. The measure carries which kind of thing stopped
     * it, and the sentence for one is a report's — written where the finding was made, an English
     * phrase travelled inside the finding, which is how a value that was never words came to be
     * printed by whoever called {@code String.valueOf} on it.
     */
    private static String whyUnread(souther.compiler.partition.UndividedPosition.Reason reason) {
        return switch (reason) {
            // The three a rule reaches, written about the rule: the line these appear on names it,
            // so a sentence saying "a rule about it" would name the rule and then not say so.
            case UNSUPPORTED_SYNTAX -> "written in a form this compiler does not read";
            case UNSUPPORTED_DOMAIN -> "compared against values no line can be drawn on here";
            case COMPETING_COORDINATES ->
                    "a rule beside it is about the position's other coordinate, so neither can be"
                            + " chosen";
            case UNSUPPORTED_PARTITION_SHAPE ->
                    "it relates two positions rather than dividing one";
            case RULE_ABOUT_A_DERIVED_VALUE ->
                    "it is about a value made from this one, and what it says about the values here"
                            + " is not worked out";
            case RULE_CUTS_NOTHING ->
                    "it was read to the end and cuts nothing this position appears in";
            case RULE_CUTS_OUTSIDE_WHAT_THE_QUANTITY_HOLDS ->
                    "it was read to the end and draws its line outside what the quantity it cuts"
                            + " ever holds";
            // And the four a position reaches, written about the position, because that is all
            // there is: nothing observed a rule to name. Which reasons reach which of the two is
            // settled by the authority a reason belongs to
            // ({@link souther.compiler.inputs.BlockReason}), so no reason is written both ways.
            case RULES_NOT_READ_AT_ALL -> "the rules written about it were not reached at all";
            case DEPTH_LIMIT -> "the walk stopped before reaching what is under it";
            case TYPE_UNRESOLVED -> "its type could not be worked out here";
            case UNSUPPORTED_TRAVERSAL ->
                    "its values are held inside something this does not reach into";
        };
    }

    /** What a rule raised, in the words this document promises its reader. Here for the reason
     *  {@link #whyUnread} gives. */
    private static String asked(souther.compiler.check.CoverageObligation question) {
        return switch (question) {
            case ADMITTED_VALUES -> "which values may stand at";
            case BOUNDARY -> "where the values stop on";
        };
    }

    /**
     * Which of the names a question carries a reader is shown.
     *
     * <p>The reader's choice and not the measure's. What a line falls on is shown where there is
     * one, since that is what tells two questions at one position apart; the position is what is
     * left.
     */
    private static String subjectOf(souther.compiler.query.PartitionEvidence.Unanswered asked,
                                    SourceNameResolver names, SourceId declaredIn) {
        return asked.measure() != null ? asked.measure() : asked.at();
    }

    /**
     * Which arms of the body the rows go through.
     *
     * <p>Called the arms, and never the paths. Going through both arms of two nested conditions is four
     * arms and says nothing about their combinations, and a report that said "paths covered" would
     * invite an author to stop looking exactly where there is more to find.
     */
    void branch(StringBuilder out, BehaviorReport behavior,
                               SourceId declaredIn, SourceNameResolver names) {
        Adequacy.BranchEvidence branch = behavior.branch();
        if (branch == null) {
            return;
        }
        ReportMeasurement<Adequacy.BranchEvidence.Arms> measured =
                ReportMeasurement.of(branch.measured());
        if (!measured.counted()) {
            // The measure's own answer, translated. Nothing here works out why from the row count or
            // the kind of behavior: those correlate with the reason and are not it, and the line an
            // author reads is the one place that difference shows.
            String said = switch (measured.reason()) {
                // Each way of owing no arm in its own words. One switch and not a word per measure,
                // so a reason added later stops here and is decided about.
                case Adequacy.BranchEvidence.NoArms it -> switch (it) {
                    case NO_BODY -> "not applicable (this behavior has no body)";
                    case NO_ARM_OBLIGATIONS -> "not applicable (this body owes no arm)";
                };
                case Adequacy.BranchEvidence.Unreadable _ ->
                        "not measured (the arms could not be read)";
                // The model says this behavior writes a body. What it owes is unknown rather than
                // nothing, which is the difference this line exists to show.
                case Adequacy.BranchEvidence.Unelaborated _ ->
                        "not measured (this module's bodies were not elaborated)";
                case Adequacy.BranchEvidence.NotAsked it ->
                        // The one measure a report says nothing about, because it is not a measure
                        // of this report: what was asked for is an input to the whole run, and a
                        // line repeating it against every behavior says one fact as many times as
                        // the module has behaviors. Every other way of having no number is about
                        // this behavior and is said here.
                        it == Adequacy.BranchEvidence.NotAsked.NO_ROWS
                                ? "not measured (no row names this behavior)" : null;
                // Not a `null` for whatever is left. The arm measure carries one of the four reason
                // types above and nothing else, so a fifth arriving here is a reason nobody decided
                // a word for — and answered with `null` it would leave the line out altogether,
                // which is the measure going quiet about a number it does not have.
                default -> throw new IllegalStateException(
                        "the arm measure has no word for " + measured.reason());
            };
            if (said != null) {
                out.append(String.format("    branch      %s%n", said));
            }
            return;
        }
        // Two questions and two answers. Whether every row could be read is what says an arm
        // nothing was seen to reach may still be reached; whether the numbers are a whole measure
        // falls for that and for a fork whose rule could not be worked out as well. Read as one, a
        // build whose rows all ran was told a row was not read, and every arm it certainly does not
        // reach went unsaid.
        //
        // The same two answers this document's JSON is written from, and not the same decision
        // about what to show: a person reading a line has room for a number and a word qualifying
        // it, so the counts are printed under a reading that did not finish and the qualification
        // is printed beside them. What is shared is where the numbers come from (issue #997).
        //
        // Asked of the one thing that answers it. This surface prints the arms out of the findings,
        // which carry the places to send a reader, so what it needs here is whether the claim stands
        // at all — and that is the same question, put to the same measure, as the one whose answer
        // the findings and the JSON are made of. A capability accessor beside the arms would be a
        // second thing to keep in step with them.
        boolean observed = branch.unreached().isPresent();
        Adequacy.BranchEvidence.Arms arms = measured.get();
        out.append(String.format("    branch      %d/%d%s%n", arms.coveredObligations(),
                arms.obligations(), observed ? "" : "   (undecided: a row was not read)"));
        // The position alone where the arm is in the module's own source, which the section this is
        // under already names. It is not always: a body is spliced into whatever calls it, so an arm
        // written in a helper another module declares is in that module's file, and there the file is
        // named with it. Named only where every row was read: an arm a row that never finished might
        // have gone through is undecided, and calling it unreached sends the author after a row that
        // exists.
        // Arms this counts as one that it cannot show are one. Said before the arms nothing
        // reaches, since it qualifies the number above rather than adding to what is missing from
        // it: a count holding two predicates where it says one is what would otherwise report a
        // behavior complete over something nothing ran.
        for (souther.compiler.types.CoverageOrigin together : branch.unsettledDecisions()) {
            out.append(String.format(
                    "      · a fork `%s` wrote decides by a rule its caller supplies, and which"
                            + " rule decides here could not be worked out: what its arms come to is"
                            + " read over however many rules that is%n",
                    together.module()));
        }
        // Whatever findings there are, and no second opinion about whether there may be any. Which
        // arms may be named is settled where they are collected, so a measure that cannot make the
        // claim produces none of these — and a condition repeated here would be the same rule kept
        // in two places, which is how the reading and the numbers came to disagree before.
        for (Adequacy.Finding f : behavior.findings()) {
            if (f.about() instanceof About.AnArmNoRowGoesThrough(var arm)) {
                out.append(String.format("      %s no row goes through `%s` (%s)%n",
                        mark(f), ArmVocabulary.label(arm), f.at().said(names, declaredIn)));
            }
        }
    }

    /**
     * The pair numbers as counts, never as one ratio.
     *
     * <p>A ratio needs a denominator that is known, and this one is not: a combination no row sits in
     * has not been shown unreachable, only untried. Printing 3/8 would read as five gaps when it may
     * be five impossibilities.
     */
    private static String combinations(PartitionEvidence.PairSpace pairs) {
        if (pairs == null || pairs.total() == 0 || pairs.counted().made().isEmpty()) {
            return "";
        }
        // A space too large to walk says so, and says it from what weakened the measurement rather
        // than from a flag kept beside it that had to be held in step.
        if (pairs.counted().weakening().causes().stream()
                .anyMatch(Weakening.PairSpaceTruncated.class::isInstance)) {
            return String.format("pairs %d, too many to enumerate", pairs.total());
        }
        PartitionEvidence.PairSpace.PairCounts counts = pairs.counted().made().orElseThrow();
        boolean whole = pairs.counted() instanceof Measurement.Complete<?>;
        if (pairs.decided()) {
            return String.format("pairs %d/%d", counts.covered(), pairs.total());
        }
        // Untried where every row was read, undecided where some were not: a combination an unread
        // row may sit in has not been left untried by anybody.
        return String.format("pairs %d reached / %d known reachable, %d %s",
                counts.covered(), counts.witnessedFeasible(), counts.unknown(),
                whole ? "untried" : "undecided");
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

    private static String whyNoAxis(souther.compiler.observe.MeasureReason reason) {
        return switch (reason) {
            case PartitionEvidence.AxisCoverage.NoRows _ -> "no row names this behavior";
            case souther.compiler.query.NothingWasAsked _ -> "nothing was asked for";
            default -> reason.name();
        };
    }

    /**
     * That a measure with numbers was not made in full, where it was not.
     *
     * <p>The numbers alone read the same either way, which is the thing this whole measure-level
     * answer is against: a behavior one of whose rules this compiler could not read showed the line
     * it did draw and the same {@code borders 1   coverage items 4/4} a model read to the end gets.
     * Why it was not is beside it already — the rules nothing took in, the positions the walk
     * could not reach into — so this says which measure they cost rather than saying them again.
     */
    private static String inFull(MeasurementStatus status) {
        return status == MeasurementStatus.PARTIAL ? "   (not all of it was measured)" : "";
    }

    /**
     * Why a measure with no number has none, in the words a document promises.
     *
     * <p>Said of the rules and not of their absence. A behavior whose only rule about a pair of
     * positions relates them has rules — printed a line above, by name — and they divide no
     * position and draw no line; a sentence saying the model has none would read as contradicting
     * the rule beside it.
     */
    private static String whyNoPartition(souther.compiler.observe.MeasureReason reason) {
        return switch (reason) {
            case souther.compiler.query.PartitionDerivation.TheReadingDidNotRunOut _ ->
                    "not measured (no partition axis was derived at any position)";
            case souther.compiler.query.PartitionDerivation.NothingIsDivided _ ->
                    "not applicable (the rules of this behavior divide no position)";
            case souther.compiler.query.PartitionDerivation.NoSubject _ ->
                    "not applicable (this behavior is measured at its stages)";
            default -> reason.name();
        };
    }

    private static String whyNoBoundary(souther.compiler.observe.MeasureReason reason) {
        return switch (reason) {
            case souther.compiler.query.BoundaryDerivation.TheReadingDidNotRunOut _ ->
                    "not measured (no line was derived at any position)";
            case souther.compiler.query.BoundaryDerivation.NoRuleDrawsALine _ ->
                    "not applicable (the rules of this behavior draw no line)";
            case souther.compiler.query.BoundaryDerivation.NoSubject _ ->
                    "not applicable (this behavior is measured at its stages)";
            default -> reason.name();
        };
    }

    /** What the search for a value at an edge came to, where it ran and found none. */
    private static String whatWasTried(ItemAssessment.Attempt attempt, SourceNameResolver names,
                                       SourceId declaredIn) {
        if (!(attempt instanceof ItemAssessment.Attempt.Unresolved left)) {
            return "";   // nothing ran, and what a run would have said is not this line's to guess
        }
        // A proof is not a failure, and the sentence in front of the reason may not say it is.
        // Every other word here is this compiler saying what it did not manage; one of them is the
        // model settling the point, and reading them under one opening sends an author looking for
        // a row nothing can write. Asked of the reason, which is where that decision is written.
        String opening = left.why().reason().provesInfeasible()
                ? " — " : " — nothing composed one: ";
        return opening + left.why().said().orElseGet(() -> whyUnresolved(left.why()))
                + whatTheRegionLeftOut(left.unaccountedFor(), names, declaredIn);
    }

    /**
     * What the search ran over that the way to the border does not account for, where anything did.
     *
     * <p>Which conditions those are, and whether this outcome is one they bear on, is
     * {@link ItemAssessment.Attempt#unaccountedFor()}'s — so what is left here is the wording. A
     * report deciding it would be a second reader of the same two facts, and the only way to ask
     * what it decided would be to compile a model that produces this sentence.
     *
     * <p>What is said is what is known: these conditions are not represented in the region. Not
     * that the region is wider than the rows that reach the line — a condition nothing could take
     * in may be implied by the ones that were, or may hold of every row — and a sentence claiming
     * the wider box would be this report deciding something it has not been shown.
     */
    private static String whatTheRegionLeftOut(
            List<souther.compiler.partition.OnTheWay.Declined> left,
            SourceNameResolver names, SourceId declaredIn) {
        if (left.isEmpty()) {
            return "";
        }
        StringBuilder out = new StringBuilder("; not every condition on the way to the line is"
                + " represented in the region searched: ");
        for (int i = 0; i < left.size(); i++) {
            out.append(i == 0 ? "" : ", ")
                    .append(whyDeclined(left.get(i).why()))
                    // The place last and in brackets, as every other line of this report writes
                    // one. Written into the sentence, it lands after a verb and reads as part of
                    // what the sentence says rather than as where to look.
                    .append(" (").append(left.get(i).at().said(names, declaredIn)).append(")");
        }
        return out.toString();
    }

    /**
     * What stopped one condition on the way from narrowing the search, in the words a reader acts
     * on.
     *
     * <p>One phrase per shape rather than one for all three. What an author does about a condition
     * this reading has no words for is not what they do about a comparison it could not turn into a
     * cut, and neither is what they do about an arm that states one of two things — a single "was
     * not read" for all of them is the vocabulary being kept apart in the compiler and put back
     * together on the way out.
     */
    private static String whyDeclined(souther.compiler.partition.OnTheWay.Why why) {
        // Noun phrases, because what the line above them says is "not every condition ... is
        // represented", and each of these names one of those conditions. Written as sentences, the
        // place in brackets after them lands after a verb and reads as part of what is being said
        // rather than as where to look.
        return switch (why) {
            case souther.compiler.partition.OnTheWay.Why.NoWordsForTheShape _ ->
                    "a condition that is neither a comparison nor a combination of them";
            // Not the words a comparison gets for drawing no line: that answers why there is no
            // boundary, and its answers are wrong about this — a comparison of two constants is a
            // form nothing reads there, and a form this arithmetic cannot carry is a relation
            // between positions there, which is something a cut carries perfectly well.
            case souther.compiler.partition.OnTheWay.Why.ComparisonNotRepresentedAsACut _ ->
                    "a comparison this reading could not turn into a cut";
            case souther.compiler.partition.OnTheWay.Why.OneOfTwoThings _ ->
                    "an outcome that states one of two things";
        };
    }

    /** The category a search came back with, where the class it was about said nothing itself. */
    private static String whyUnresolved(souther.compiler.partition.Generator.UnresolvedCombination why) {
        String at = why.subject();
        return switch (why.reason()) {
            case NOTHING_COMPOSES_ONE -> "nothing here could build a representative for " + at;
            case ALL_CANDIDATES_REJECTED -> "every value tried at " + at + " was refused";
            case SEARCH_LIMIT -> "the search stopped before reaching " + at;
            // What is missing here, and not what cannot exist. The combinations are there and this
            // declined to walk them, so a reader is told the offer was not made rather than that
            // nothing reaches the arm — and told that raising the row budget is not what lifts it.
            case THE_GROUP_WAS_NOT_OFFERED ->
                    "the decisions that settle " + at + " have more combinations together than this"
                            + " offers a row for, so none of them was looked in";
            // What the partition divides this body's positions into, and not whether a run gets
            // there. Some decision on the way places at no class, so there is nothing to put a
            // value at that steers a row along it — a row put at what the rest of the way leaves
            // may go the other way round that fork.
            case THE_WAY_IN_PLACES_AT_NO_CLASS ->
                    "the way to " + at + " holds a decision that no class of any position stands"
                            + " for, so nothing here can steer a row along it";
            case THE_RULES_LEAVE_NOTHING_THERE ->
                    "the rules leave no value at " + at;
            // What the model settles, said as that. A class under one case of a sum and a class
            // under another are classes of positions that are not in one value, so there is no row
            // to go looking for.
            case ONE_POSITION_CANNOT_BE_BOTH ->
                    at + " would need one position to be two things at once, which no value is";
            case NOTHING_TO_BUILD_AGAINST -> "there was nothing to build a candidate against";
            case NO_VALUES_WERE_ASKED_FOR ->
                    "this build composed no values, so no row was written for " + at;
            case LINKAGE_FAILED -> "the generated classes would not link";
            case NO_CERTIFIED_WITNESS ->
                    "no row composed for " + at + " was seen reaching it, which does not make the"
                            + " combination unreachable";
            case THE_POSITION_WAS_WITHHELD ->
                    "a row's value at that position could not be read, so no class of it was"
                            + " looked for";
            case THE_ROWS_WERE_NOT_READ -> "the rows were not read, so nothing was looked for";
            case NO_CANDIDATE_WAS_OFFERED ->
                    "the walk over what could stand there put no value forward";
            // What this run could look at, and not what the line admits. A line is owed once over
            // every behavior carrying the type, and the search of every one this asked about had
            // no answer — so nothing was looked for at the point.
            case NO_READING_OF_THE_LINE_COULD_BE_SEARCHED ->
                    "no reading of the line this asked about could be searched, so nothing was"
                            + " looked for at " + at;
        };
    }

    private static String whyNoBoundaryItem(Measurement<ItemAssessment.Coverage> coverage) {
        souther.compiler.observe.MeasureReason why = ReportMeasurement.of(coverage).reason();
        if (why == null) {
            return "";
        }
        return switch (why) {
            case ItemAssessment.Coverage.NotAsked it -> switch (it) {
                case NOT_ASKED -> "nothing was asked for";
                case ARMS_NOT_ASKED -> "the arms were not asked for";
                case NO_ROWS -> "no row names this behavior";
            };
            case ItemAssessment.Coverage.CouldNotAsk _ -> "the arms could not be measured";
            default -> why.name();
        };
    }

    private static final JsonMapper JSON = JsonMapper.builder().build();

    /**
     * One measurement in the word a document uses.
     *
     * <p>Public because it is the projection, and the projection is the only thing that turns the
     * states into words. A caller outside this package that wants the word asks here; one that
     * wants the state asks the measure, which is what the arms are for.
     */
    public static MeasurementStatus statusOf(Measure<?> measure) {
        return ReportMeasurement.of(measure).status();
    }

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

    /** The same of a word held as a constant, which is what a reason that costs a proof to say has
     *  instead of an enum name. */
    public static String word(String constant) {
        return constant.toLowerCase(java.util.Locale.ROOT);
    }

    /** The same of a reason, which is not always an enum: one that costs a proof to say carries it,
     *  and a record is what holds a proof. The word is the reason's own either way. */
    public static String word(souther.compiler.observe.MeasureReason reason) {
        return reason.name().toLowerCase(java.util.Locale.ROOT);
    }

    /**
     * Whether the partition measure is the one that answers this question.
     *
     * <p>Asked of the question and not decided here. Which measure answers a question is the
     * question's own answer ({@link souther.compiler.check.CoverageObligation#answeredBy}), and the
     * measures read the same table to know what they are short of. Filed by what the question asks
     * and not by which producer raised it.
     */
    private static boolean aboutTheClasses(souther.compiler.check.CoverageObligation question) {
        return question.answeredBy()
                == souther.compiler.check.CoverageObligation.Measure.PARTITION;
    }

    /**
     * The questions a section is the reader of, each named by the rule that raised it.
     *
     * <p>One finding kind, filed by what it asks. Which measure answers a question is settled where
     * the question is raised; a report chooses where to print it, and nothing here decides what the
     * model asked.
     */
    private void unaccounted(StringBuilder out, BehaviorReport behavior,
                                    SourceNameResolver names,
                                    souther.compiler.source.SourceId declaredIn,
                                    java.util.function.Predicate<
                                            souther.compiler.check.CoverageObligation> mine) {

        for (Adequacy.Finding f : behavior.findings()) {
            if (f.about() instanceof About.AQuestionNothingAnswered(var asked)
                    && mine.test(asked.question())) {
                out.append(String.format("      %s not accounted for: %s — %s %s%n",
                        mark(f), cited(asked.cited(), names, declaredIn),
                        asked(asked.question()), subjectOf(asked, names, declaredIn)));
            }
        }
    }

    /**
     * How a report writes the rule a question is about.
     *
     * <p>A name where the author gave one and a place where they did not, which is the same handle
     * a border prints for the line a comparison drew — the two share the formatter and the words,
     * and nothing else. What they must not share is an identity: where a rule was read is the
     * partition's and one rule has as many of those as it has readings.
     */
    private static String cited(souther.compiler.check.RuleCitation cited,
                                SourceNameResolver names,
                                souther.compiler.source.SourceId declaredIn) {
        return cited.said(names, declaredIn);
    }

    /**
     * What tells one rule of the model from another, as this document carries it.
     *
     * <p>The parts that are the identity and no more. A rule is a clause of an invariant, a
     * comparison written in a body, or a rule of an {@code ensures} clause, and each is told from
     * its neighbours by different coordinates — so this is an object per kind rather than one
     * spelling every kind is squeezed into. Not the internal value's own words: what a compiler
     * calls a rule to itself is not a contract, and this is.
     *
     * <p>Not a name and never shown to a reader. `rule` beside it is what an author is given, and
     * the two are different questions: a handle finds a rule and an identity distinguishes one.
     */
    private static void ruleId(ObjectNode into, souther.compiler.check.RuleRef rule) {
        into.put("kind", schemaRuleKind(rule));
        // Every part of the identity and not the parts that read well. A declaration is its module
        // and its name — two modules may each declare an `Amount` and they are two types — and a
        // construct is numbered from zero in each source, so the module is what tells one behavior's
        // twelfth construct from another's. Written without them, two rules of two modules project
        // onto one identity, which is the one thing this field may not do.
        switch (rule) {
            // The clause, by the declaration it is written on and its place among that
            // declaration's clauses — which is how somebody reading the declaration counts them.
            case souther.compiler.check.RuleRef.Invariant it -> {
                into.put("declaredIn", it.clause().id().declaredOn().module());
                into.put("declaredOn", it.clause().id().declaredOn().name());
                into.put("clause", it.clause().id().ordinal());
            }
            // The rule of the clause, by the behavior it is declared on and where it sits among the
            // clauses and their arms. Two arms naming one case are two rules and differ here.
            case souther.compiler.check.RuleRef.Ensures it -> {
                into.put("declaredIn", it.rule().behavior().module());
                into.put("behavior", it.rule().behavior().name());
                into.put("clause", it.rule().clause());
                into.put("arm", it.rule().arm());
            }
            // The comparison, by the behavior it is written in and the construct it was numbered
            // as. The numbering starts at zero in each source, so the source is part of it.
            case souther.compiler.check.RuleRef.Comparison it -> {
                into.put("declaredIn", it.origin().module());
                into.put("behavior", it.behavior());
                into.put("ordinal", it.origin().ordinal());
                into.put("lowered", it.origin().lowered());
            }
        }
    }

    /**
     * How schema 3 spells which kind of rule an identity is of.
     *
     * <p>A wire value and not a word for the rule, which is what the name used to say. What a rule
     * is called is {@link souther.compiler.check.RuleCitation}'s answer, and the two say one thing
     * again as of version 4 — they are still separate values, because what a document groups by is a
     * contract a version pins and what a reader is shown is not.
     *
     * <p>Here rather than at the one place it is written, for the reason the others are. No
     * {@code default}, so a rule shape added and not given a spelling stops the compile rather than
     * arriving in a document as one that already existed.
     */
    public static String schemaRuleKind(souther.compiler.check.RuleRef rule) {
        return switch (rule) {
            case souther.compiler.check.RuleRef.Invariant _ -> "invariant";
            case souther.compiler.check.RuleRef.Ensures _ -> "ensures";
            // The rule and not the construct it is written in. A comparison may stand in the
            // condition of an `if` or a `guard`, be given a name above the fork that tests it, or be
            // what the behavior answers with, and it is one rule in all of those — so `guard` was a
            // word for where some of them happen to be written, and false of the rest. Documents of
            // version 3 carry `guard` here; the word moved with the version rather than under one,
            // because a document already written groups by what it was told.
            case souther.compiler.check.RuleRef.Comparison _ -> "comparison";
        };
    }

    /**
     * The word a document writes for which kind of thing a question is about.
     *
     * <p>Here rather than at the one place it is written, for the reason the others are: a reader
     * holding the arms can be held to the words without reading the writer. No {@code default}, so
     * an arm added and not given a word stops the compile rather than arriving in a document as one
     * that already existed.
     */
    public static String subjectWord(souther.compiler.inputs.InputQuestion asks) {
        return switch (asks) {
            case souther.compiler.inputs.InputQuestion.AboutAPosition _,
                 souther.compiler.inputs.InputQuestion.AboutANumber _ -> "position";
        };
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
        root.put("status", wire(status()));
        weakening(root, weakenedBy);
        root.put("adequacy", word(adequacy()));
        ArrayNode modulesOut = root.putArray("modules");
        for (ModuleReport module : modules) {
            ObjectNode m = modulesOut.addObject();
            m.put("module", module.module());
            m.put("status", wire(module.status()));
            weakening(m, module.weakenedBy());
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
            // What the module's declarations are short of, beside what its bodies are. A line an
            // `invariant` drew is not any behavior's, so publishing it under one would publish it
            // under whichever a walk reached first — and left out, a consumer counting what a build
            // refuses over would come up short of what the page shows (issue #1062).
            //
            // Under the declaration that owes it, the way a behavior's findings are under the
            // behavior. What a finding says of itself is what the line asks of a row, and two
            // declarations bounding a string's length at one say it the same way — so published as
            // one flat list they are two identical objects, and which declaration a reader is being
            // sent to is exactly what {@link souther.compiler.query.FindingSubject} was introduced
            // to keep.
            declarations(m.putArray("declarations"), module.declarations(), sources);
            ArrayNode behaviors = m.putArray("behaviors");
            for (BehaviorReport behavior : module.behaviors()) {
                ObjectNode b = behaviors.addObject();
                b.put("name", behavior.name());
                b.put("implementation", behavior.implementation().written());
                // Written where the rows were read, and left out where they were not. A zero here
                // is a behavior whose rows were read and numbered none of them, which a consumer
                // acts on differently from rows nobody read.
                behavior.rows().ifPresent(count -> b.put("rows", count));
                behavior.pending().ifPresent(count -> b.put("pending", count));
                b.put("status", wire(behavior.status()));
                weakening(b, behavior.weakenedBy());
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
        // A behavior with no signature to read has no section, which is what this document has
        // always said the absence of one means. Written out instead, the section would owe an
        // `inputs` array of the positions — and how many there are is read off the very boundary
        // that was not worked out, so a `>->` composition would publish an empty one and say that
        // it takes nothing. Which behavior it happened to and what it cost is the behavior's
        // `weakening`, where it is one fact rather than one per measure that went without it.
        if (signature.boundaryNotDerived()) {
            return;
        }
        ObjectNode out = behavior.putObject("signature");
        measured(out, signature.counted());
        ObjectNode output = out.putObject("output");
        // What the type declares is the model's and is written whether or not anybody wrote a row.
        // What the rows reached is the measurement's, and where there is none there is nothing to
        // write — four empty arrays and a zero used to say the same as a behavior every case of
        // which went uncovered.
        names(output.putArray("declared"), signature.output().declared());
        measured(output, signature.output().cases(), (node, cases) -> {
            names(node.putArray("specified"), cases.specified());
            names(node.putArray("observed"), cases.observed());
            names(node.putArray("verified"), cases.verified());
            node.put("unclassifiedRows", cases.unclassifiedRows());
        });
        ArrayNode inputs = out.putArray("inputs");
        // Every position, and this section is written only where they were counted. The one state
        // that has none to write is the one that returns above.
        for (InputCaseEvidence input : signature.positions()) {
            ObjectNode in = inputs.addObject();
            names(in.putArray("declared"), input.declared());
            names(in.putArray("excluded"), input.excluded());
            measured(in, input.cases(), (node, cases) -> {
                names(node.putArray("specified"), cases.specified());
                names(node.putArray("executed"), cases.executed());
                names(node.putArray("verified"), cases.verified());
                node.put("unclassifiedRows", cases.unclassifiedRows());
            });
        }
    }

    private void partition(ObjectNode behavior, PartitionEvidence partition,
                                  ClaimAnnotations claimed, DocumentSources sources) {
        // The one decision, the same one the page reads. Written here as well, the two surfaces
        // answered a reader differently about which behaviors have a section at all.
        if (!(PartitionSection.of(partition) instanceof PartitionSection.Present)) {
            return;
        }
        ObjectNode out = behavior.putObject("partition");
        // Each measure's own answer, beside the entries it answered with. Read off the arrays alone,
        // a reader has the same two empties this report used to confuse: a behavior with no
        // positions to divide and one whose positions could not be read both write `[]`, and only
        // this says which. `branch` has carried its own status from the first version; these two are
        // the same measure-level fact in the one place that had nowhere to put it.
        measured(out.putObject("axesMeasure"),
                partition.partitioned());
        measured(out.putObject("boundariesMeasure"),
                partition.bounded());
        ArrayNode axes = out.putArray("axes");
        for (PartitionEvidence.AxisCoverage axis : partition.axes()) {
            ObjectNode a = axes.addObject();
            a.put("axis", axis.at().toString());
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
            axis.classes().forEach(a.putArray("classes")::add);
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
            // Only where there is a measurement. A position nothing was measured at used to write
            // an empty `covered` and a zero count, which reads exactly like one where every class
            // went unreached — the `status` beside them said which and nothing made a reader look.
            measured(a, axis.reached(), (node, reached) -> {
                reached.covered().stream().sorted().forEach(node.putArray("covered")::add);
                node.put("unclassifiedRows", reached.unclassifiedRows());
            });
        }
        // The questions the model raised that nothing answered, beside the measures rather than
        // inside one. Every measure here is a reader of them, and a position no axis came back for
        // still has whatever was written about it.
        if (!partition.unanswered().isEmpty()) {
            ArrayNode standing = out.putArray("unanswered");
            for (PartitionEvidence.Unanswered each : partition.unanswered()) {
                ObjectNode one = standing.addObject();
                one.put("at", each.at());
                // The rendered label, which is what this key has always been. What it is rendered
                // from is beside it: a name is a name, and a place is a place, and a consumer that
                // needs to open a file wants the second rather than a string to take apart.
                // The same handle the border prints for a line the comparison drew, through the
                // table of sources this document carries.
                one.put("rule", each.cited().said(sources::written, null));
                // What tells one rule from another, beside the words for finding it. A handle is a
                // projection of the rule and not the rule: two arms of one `ensures` clause may
                // name the same case, so the author's words for them are the same words, and two
                // questions came out as one object twice. Within this document and not a name to
                // show a reader — which is what `rule` beside it is.
                ruleId(one.putObject("ruleId"), each.rule());
                one.put("question", word(each.question()));
                // What the question is about, as the question names it. The number a line falls on
                // is beside the position rather than in place of it, because a rule about the
                // length of a string is a rule at that string: an author looking for where it is
                // written looks at the position, and what the line is on is the other half of the
                // answer.
                ObjectNode about = one.putObject("subject");
                about.put("kind", subjectWord(each.asks()));
                about.put("path", each.at());
                if (each.measure() != null) {
                    about.put("measure", each.measure());
                }
            }
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
        for (BorderAssessment boundary : partition.boundaries()) {
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
            b.put("origin", boundary.describe(sources::written, null));
            // What the line is a line at, said rather than left to be inferred from the text beside
            // it. A line between two positions writes the other position where a line at a count
            // writes the count, and the two read alike.
            b.put("kind", word(boundary.shape()));
            b.put("value", boundary.value());
            // The four coverage items, under the border that owes them. Emitted flat, the two the
            // technique keys on the border and the two it keys on the same border were an entry each
            // and nothing said which border they belonged to — a consumer working to a coverage
            // criterion had to group them back by three fields and guess at the rest.
            ArrayNode items = b.putArray("items");
            for (BorderAssessment.Point point : boundary.points()) {
                ObjectNode i = items.addObject();
                i.put("point", word(point.role()));
                switch (point.item()) {
                    // Why no row is owed, in the one word that says which of the three settled it.
                    // Absent, the two that are not shortfalls read as the report being short.
                    case ItemAssessment.NotOwed not -> i.put("notOwed", word(not.reason()));
                    case ItemAssessment.Owed owed -> {
                        // What a row here has to do, whole. Two of the four ask for a place and two
                        // ask for a side, so a document carrying a value for all four would name a
                        // witness of a side as though it were the side.
                        i.put("relation", point.border().operator(point.role()));
                        i.put("against", point.border().against(point.role()));
                        // Outside the measurement's gate, because it is not this measurement's
                        // answer. What settles it is its own body of evidence, only one ground of
                        // which the coverage measure reads. So a point nobody measured can carry
                        // `knownWritable: true` beside a status saying so, and the two are
                        // consistent: one says whether a row can be written here and the other
                        // whether anybody looked for one (issue #997).
                        //
                        // The grounds beside the verdict, and the verdict kept. Two of the three are
                        // nowhere else in this document — the attempt is the human surface's and
                        // `--generate`'s — so a reader given only the boolean cannot tell a point
                        // the rules prove inhabited, which stands whatever any search afterwards
                        // makes of it, from one a search happened to reach. The two license
                        // different sentences (issue #1036).
                        ItemAssessment.WritabilityEvidence evidence = owed.writabilityEvidence();
                        i.put("knownWritable", evidence.known());
                        // In this document's own order, which is why it is written down here and
                        // not asked of the evidence. The grounds are a set and have none, so some
                        // order has to be chosen for the array — and chosen where the array is, the
                        // choice is not one an editor moving two constants apart can make.
                        ArrayNode because = i.putArray("writableBecause");
                        for (ItemAssessment.WritabilityEvidence.Ground ground : GROUND_ORDER) {
                            if (evidence.has(ground)) {
                                because.add(wire(ground));
                            }
                        }
                        // Inside it, because it is. `false` here is `NoHit` — what the rows this
                        // measurement read came to — and never a measurement that was not made.
                        measured(i, owed.coverage(), (node, coverage) ->
                                node.put("hit", ItemAssessment.Coverage.hit(coverage)));
                    }
                }
            }
        }
        ObjectNode pairs = out.putObject("pairs");
        // The size of the space is the model's and is written whether or not anybody counted. The
        // counts are the measurement's and are written only where one was made; `truncated` is gone
        // from here entirely, since a space too large to walk says so under `weakening`.
        pairs.put("total", partition.pairs().total());
        measured(pairs, partition.pairs().counted(), (node, counts) -> {
            node.put("covered", counts.covered());
            node.put("witnessedFeasible", counts.witnessedFeasible());
            node.put("provenInfeasible", counts.provenInfeasible());
            node.put("unknown", counts.unknown());
        });
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
            // And which rule, where one was read and could not be used. Absent where the reading
            // never arrived at the rules of the position: there is nothing to name, and a field
            // holding a placeholder would say this compiler had looked at a rule it never saw.
            // Present, the pair is this: `rule` is the handle an author acts on and `ruleId` is
            // what tells one rule from another, and the two are not in step wherever a rule has no
            // name of its own.
            if (each instanceof PartitionEvidence.NotRead.ARule rule) {
                said.put("rule", rule.cited().said(sources::written, null));
                ruleId(said.putObject("ruleId"), rule.rule());
            }
        });
    }

    static void branch(ObjectNode behavior, Adequacy.BranchEvidence branch,
                               DocumentSources sources) {
        if (branch == null) {
            return;
        }
        ObjectNode out = behavior.putObject("branch");
        measured(out, branch.measured(), (node, arms) -> {
            node.put("arms", arms.obligations());
            node.put("covered", arms.coveredObligations());
            // Arms counted as one that nothing can show are one, which qualifies the two numbers
            // above. Said here as well as in the prose, since a count that quietly holds two
            // predicates where it says one is the shape a consumer would read as a behavior
            // complete over something nothing ran — and a consumer reads this and not the prose.
            //
            // Inside the gate although it is the measurement's own answer rather than this value's,
            // because what it qualifies is the two counts. Where they are not written there is
            // nothing for it to qualify, and an empty array beside no numbers is an empty set
            // standing in for a measurement nobody made (issue #997).
            ArrayNode together = node.putArray("unsettledDecisions");
            for (souther.compiler.types.CoverageOrigin each : branch.unsettledDecisions()) {
                together.add(each.module());
            }
            // A second question, and the measure answers it rather than this deciding. The first is
            // whether there is a value; this is whether a negative claim over it stands, and the
            // measure hands the arms over only where it does. Written here as a condition on the
            // value, this line would be a rule kept by whoever wrote the next surface.
            //
            // Absent rather than empty where it does not. `[]` reads as "no arm goes unreached",
            // which is a finding, and writing it for a reading that found nothing out is the same
            // substitution as the counts this measure used to write for a measurement nobody made.
            branch.unreached().ifPresent(missed -> {
                ArrayNode unreached = node.putArray("unreached");
                for (souther.compiler.coverage.CoverageSites.Site arm : missed) {
                    ObjectNode a = unreached.addObject();
                    a.put("label", ArmVocabulary.label(arm));
                    a.put("kind", word(arm.name()));
                    // What the arm is an outcome of. Two fields because the meaning is the pair: an
                    // `else` an author wrote under an `if` and one written under a `guard` are the
                    // same outcome of two constructs, and a consumer told only the outcome cannot
                    // tell them apart.
                    a.put("construct", word(arm.construct()));
                    at(a, arm.at(), sources);
                }
            });
        });
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
    private void findings(ObjectNode behavior, BehaviorReport of, DocumentSources sources) {
        findings(behavior.putArray("findings"), of.findings(), sources);
    }

    /**
     * What each declaration of the module is short of, under the declaration.
     *
     * <p>The grouping a human report prints, published. A finding carries which declaration it is
     * about, so this is a rendering of that and not a second answer: read off the entries alone, the
     * subject a finding writes is what the line asks of a row, and the declaration it belongs to
     * would be gone.
     */
    private void declarations(ArrayNode out, List<Adequacy.Finding> written,
                              DocumentSources sources) {
        Map<String, List<Adequacy.Finding>> byDeclaration = new LinkedHashMap<>();
        for (Adequacy.Finding each : written) {
            byDeclaration.computeIfAbsent(each.named(), _ -> new ArrayList<>()).add(each);
        }
        byDeclaration.forEach((declaration, findings) -> {
            ObjectNode one = out.addObject();
            one.put("name", declaration);
            findings(one.putArray("findings"), findings, sources);
        });
    }

    /**
     * The same entries, wherever they are published.
     *
     * <p>One writer, because a finding about a declaration is published in the same fields as one
     * about a behavior — what it is about is the subject's answer and not a second shape of entry.
     * Written twice, a consumer joining on the fields would find them agreeing until one of the two
     * was edited.
     */
    private void findings(ArrayNode out, List<Adequacy.Finding> written, DocumentSources sources) {
        for (Adequacy.Finding finding : written) {
            ObjectNode f = out.addObject();
            f.put("kind", word(finding.kind()));
            f.put("disposition", word(finding.disposition(held)));
            f.put("subject", subject(finding, sources));
            // Which rule this is about, where the finding is about one. The words in `subject` are
            // how a reader finds it, and two rules an author named alike have the same words — so a
            // consumer joining findings to the questions they came from wants this.
            //
            // Asked of the subject rather than matched against the kinds that have one. Listed
            // here, a kind added and not listed wrote no identity, and one rule's findings came out
            // identical in every field with nothing to join them by.
            if (finding.about() instanceof About.OfARule about) {
                ruleId(f.putObject("ruleId"), about.rule());
            }
            // And which limit stopped it, where the finding is about one being in the way. Two
            // conjuncts of one clause about one position can stop for two different limits, so
            // written without this a rule's findings there are one object twice — and the entry
            // beside them in `notRead` is keyed on the reason, which leaves nothing to join by.
            if (finding.about() instanceof About.OfSomethingNotRead about) {
                f.put("reason", word(about.finding().reason()));
            }
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
     * about what it is about, and reading it back off a coordinate would be this report working out
     * something the measure already knew.
     */
    private static Citation placeOfItsOwn(Adequacy.Finding finding) {
        return switch (finding.about()) {
            case About.AnArmNoRowGoesThrough _ -> finding.at();
            case About.ACaseNoRowExpects _, About.ACaseNothingWasSeenToProduce _,
                    About.ACaseNoRowAppliesItTo _, About.AClassNoRowIsIn _,
                    About.APointOfABorder _, About.APointOfADeclaredBorder _,
                    About.APositionNoLineDivides _,
                    About.APositionThisCouldNotRead _, About.ARuleWithoutALine _,
                    About.AQuestionNothingAnswered _,
                    About.APositionWhoseRulesWereNotReached _,
                    About.APositionReadWiderThanItsRules _ -> null;
        };
    }

    /**
     * What one finding is about, in the one field every kind writes it in.
     *
     * <p>Spelled here per shape rather than taken from a payload in order. What a finding is about
     * is a value the measure established, and a document handing a consumer that value's fields in
     * the order some sentence took them would publish the shape of the sentence — which changes when
     * the sentence is reworded, and says nothing about which of the fields is the subject.
     *
     * <p>Written to join what is already in the document: a class name and its position are one of
     * an axis's {@code classes} under that axis, an arm's label is one in {@code branch.unreached},
     * and an axis and a value name a {@code boundaries} entry. An input's case carries its position
     * with it, because two parameters of one type give two findings a class name alone cannot tell
     * apart — and a class of a position carries its position for exactly that reason, which this
     * used to say of the inputs and not of the axes.
     */
    private static String subject(Adequacy.Finding finding, DocumentSources sources) {
        return switch (finding.about()) {
            // The label and not the arm, and the same label `branch.unreached` writes: this field
            // exists to join to that entry, and a value spelled a second way here would join to
            // nothing.
            case About.AnArmNoRowGoesThrough(var arm) -> ArmVocabulary.label(arm);
            case About.ACaseNoRowExpects(var missing) -> missing.name();
            case About.ACaseNothingWasSeenToProduce(var missing) -> missing.name();
            case About.AClassNoRowIsIn(var missing) ->
                    missing.name() + " (at " + missing.axis().path() + ")";
            case About.APositionNoLineDivides(var position) -> position.at().toString();
            case About.APositionThisCouldNotRead(var it) -> it.at();
            case About.ARuleWithoutALine(var it) -> it.at();
            case About.APositionWhoseRulesWereNotReached(var axis) -> axis.path();
            // The position, as the two above write it. What is said of it is the kind's; there is
            // no rule to name and no class this is about, so the position is the whole subject.
            case About.APositionReadWiderThanItsRules(var it) -> it.at().toString();
            // The rule and what it was left saying. Named by the position alone, two rules nothing
            // took in at one position serialised as two identical objects, and the human line named
            // them while a consumer of the document could not tell them apart.
            // Written to join the `unanswered` entry this came out of, so the rule is named by the
            // one method that names it. Spelled a second way here, the join this exists for held
            // for a rule with a name and broke for every rule found by where it is written.
            // The handle, and what tells this rule from another beside it: two arms of one clause
            // may name the same case, so the words alone joined two questions into one row.
            case About.AQuestionNothingAnswered(var asked) ->
                    asked.cited().said(sources::written, null) + " — " + asked(asked.question())
                            + " " + subjectOf(asked, sources::written, null);
            case About.ACaseNoRowAppliesItTo(var input, var missing) ->
                    missing.name() + " (in #" + (input.at() + 1) + ")";
            // What the point asks of a row, which is what joins it to one of a border's `items`.
            // Asked of the point, which is where the two readers of that name meet.
            case About.APointOfABorder(var point, var _) -> point.said();
            // The same sentence, on what the declaration wrote. A line owed once over every reading
            // of it is named by the terms the author used and not by the position some behavior met
            // it at, which is what the debt is (issue #1062).
            case About.APointOfADeclaredBorder(var debt) -> debt.said();
        };
    }

    /**
     * What a measure managed, where it managed nothing why, and what it went without.
     *
     * <p>Three fields and not one. {@code status} says whether there is a number; {@code reason}
     * says why there is not, and is absent where there is; {@code weakening} says what left the
     * measurement weaker than it looks, and is absent where nothing did.
     *
     * <p><b>The third is what makes the projection lossless.</b> Four words stand for five states,
     * and {@code unavailable} covers both a measurement nobody asked for and one that was started
     * and could not be finished. A document carrying a weakening beside {@code not measured} is
     * saying the second — which is not a not-measured with more explanation, and is what a reader of
     * this document could not get at all while the difference lived in a boolean on the reason
     * (issue #953).
     */
    private static void measured(ObjectNode of, Measure<?> measure) {
        measured(of, measure, (_, _) -> { });
    }

    /**
     * The same, together with the fields this measure's own value supplies.
     *
     * <p><b>One door.</b> Every field a document writes off what a measure made goes through here,
     * and {@code value} is called only where there is something to call it with. Written the other
     * way — a status here and an {@code ifPresent} beside it at each call site — the rule was a
     * convention, kept at five of the seven measures and forgotten at the other two, which wrote a
     * count and a boolean for measurements nobody had made (issue #997). It is not a compile-time
     * prohibition: {@code Measure.made()} is public, and a writer that wants to reach past this can.
     * What it does is leave one place to look, and make the shape of a correct measure-writer the
     * shape the next one is copied from.
     *
     * <p><b>What belongs inside and what does not.</b> Inside goes what the measure's value
     * supplies, and what qualifies that value — a count, what the count is of, the words that say
     * how to read it. Outside stays what the model says, which is true whether or not anybody
     * measured ({@code pairs.total}, a border's {@code relation} and {@code against}), and what a
     * different body of evidence establishes ({@code knownWritable} and {@code writableBecause},
     * whose grounds are {@link ItemAssessment.WritabilityEvidence.Ground} and only one of which this
     * measurement reads). The question to ask of a field is which evidence supplies it, not which
     * object it sits in.
     */
    private static <T> void measured(ObjectNode of, Measure<T> measure,
                                     java.util.function.BiConsumer<ObjectNode, T> value) {
        ReportMeasurement<T> said = ReportMeasurement.of(measure);
        of.put("status", wire(said.status()));
        if (said.reason() != null) {
            of.put("reason", word(said.reason()));
        }
        weakening(of, said.weakenedBy());
        said.ifMade(it -> value.accept(of, it));
    }

    /**
     * What a measurement went without, where it went without anything.
     *
     * <p>Written under one key at every level that has one, so a consumer reads the same shape of a
     * measure and of a module.
     *
     * <p><b>The kinds, once each.</b> Two rules this compiler could not read are two facts and one
     * word, and the word is all this field carries — which rule, which position, which row is named
     * where the document already names that thing. Written per fact the array would say
     * {@code rule_unread} five times and leave a reader counting repetitions of a word that
     * identifies nothing.
     */
    private static void weakening(ObjectNode of, WeakeningSet weakenedBy) {
        if (weakenedBy.isEmpty()) {
            return;
        }
        Set<String> words = new LinkedHashSet<>();
        for (Weakening each : weakenedBy.causes()) {
            words.add(each instanceof Weakening.ObservationIncomplete gap
                    ? word(gap.cause().code()) : word(wordFor(each)));
        }
        ArrayNode out = of.putArray("weakening");
        words.forEach(out::add);
    }

    /**
     * One weakening, as a word a consumer can count and match against the next run.
     *
     * <p>A {@code switch} with no {@code default}: an arm added is a compile error here rather than
     * a fact that quietly stops being said. What each arm is about is written where the document
     * already names that thing — a rule, a position, a row — so this says which kind it is and does
     * not restate the subject.
     */
    public static WeakeningWord wordFor(Weakening weakening) {
        return switch (weakening) {
            // Its own vocabulary, which is the observation codes. Asking this to spell it a second
            // way would be a second set of words for one fact.
            case Weakening.ObservationIncomplete _ ->
                    throw new IllegalArgumentException("an observation writes its own code");
            case Weakening.OutputCasesUnreadable _ -> WeakeningWord.OUTPUT_CASES_UNREADABLE;
            case Weakening.InputCasesUnreadable _ -> WeakeningWord.INPUT_CASES_UNREADABLE;
            case Weakening.BorderValueUnreadable _ -> WeakeningWord.BORDER_VALUE_UNREADABLE;
            case Weakening.ModelReadingIncomplete it -> switch (it.cause()) {
                case souther.compiler.partition.ClosureGap.RuleUnread _ ->
                        WeakeningWord.RULE_UNREAD;
                case souther.compiler.partition.ClosureGap.PositionNotReachedInto _ ->
                        WeakeningWord.POSITION_NOT_READ;
                case souther.compiler.partition.ClosureGap.QuestionUnanswered _ ->
                        WeakeningWord.QUESTION_UNANSWERED;
                case souther.compiler.partition.ClosureGap.RulesNotReached _ ->
                        WeakeningWord.RULES_NOT_REACHED;
            };
            case Weakening.BodiesNotElaborated _ -> WeakeningWord.BODIES_NOT_ELABORATED;
            case Weakening.BoundaryNotDerived _ -> WeakeningWord.BEHAVIOR_BOUNDARY_NOT_DERIVED;
            case Weakening.PairSpaceTruncated _ -> WeakeningWord.PAIR_SPACE_TRUNCATED;
            case Weakening.ProofContradicted _ -> WeakeningWord.PROOF_CONTRADICTED;
            case Weakening.ArmsUnsettled _ -> WeakeningWord.ARMS_UNSETTLED;
        };
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

    /**
     * The order this document writes the grounds of {@code writableBecause} in.
     *
     * <p>The document's and not the evidence's. The grounds are a set, so the array needs an order
     * the set cannot supply — read off {@code values()} it was the order two constants happen to be
     * declared in, and moving them apart would have moved the bytes of every document while a test
     * comparing against {@code values()} went on seeing nothing.
     *
     * <p>Every ground is here, which {@code theDocumentWritesEveryGroundThereIs} holds. A ground
     * added to the type and not to this list is one no document would carry, so the widening would
     * be made and nothing would say it had not arrived.
     */
    static final List<ItemAssessment.WritabilityEvidence.Ground> GROUND_ORDER = List.of(
            ItemAssessment.WritabilityEvidence.Ground.THE_RULES_PROVE_IT,
            ItemAssessment.WritabilityEvidence.Ground.A_ROW_IS_AT_IT,
            ItemAssessment.WritabilityEvidence.Ground.A_VALUE_WAS_BUILT);

    /** What a document calls a ground a row can be written at a point on. Written out for the same
     *  reason as the status above: widening what a consumer must handle is a decision about the
     *  contract, and renaming a constant is a decision about the compiler. Taken off the name, the
     *  second would silently be the first. */
    public static String wire(ItemAssessment.WritabilityEvidence.Ground ground) {
        return switch (ground) {
            case THE_RULES_PROVE_IT -> "the_rules_prove_it";
            case A_ROW_IS_AT_IT -> "a_row_is_at_it";
            case A_VALUE_WAS_BUILT -> "a_value_was_built";
        };
    }

    /** Case names, sorted: a report that changes order between runs cannot be compared between runs,
     * and the sets these come from keep the order the rows happened to arrive in. */
    private static void names(ArrayNode into, java.util.Set<TypeSymbol> cases) {
        cases.stream().map(TypeSymbol::name).sorted().forEach(into::add);
    }
}
