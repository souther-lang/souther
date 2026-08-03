package souther.compiler.query;

import souther.compiler.ExampleVerifier;
import souther.compiler.ast.Ast;
import souther.compiler.check.BehaviorRequirement;
import souther.compiler.check.Sig;
import souther.compiler.check.Symbols;
import souther.compiler.check.TypeOps;
import souther.compiler.observe.Classification;
import souther.compiler.observe.Disposition;
import souther.compiler.observe.Incompleteness;
import souther.compiler.observe.InputCaseEvidence;
import souther.compiler.observe.MeasurementStatus;
import souther.compiler.observe.OutputCaseEvidence;
import souther.compiler.observe.RowOutcome;
import souther.compiler.observe.Stage;
import souther.compiler.partition.Axis;
import souther.compiler.partition.AxisId;
import souther.compiler.partition.BoundaryObligation;
import souther.compiler.partition.Generator;
import souther.compiler.partition.RowClasses;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/** How well a module's {@code example} rows cover what it declares. */
public final class Adequacy {

    /**
     * How much of this a build asked to be told.
     *
     * <p>Off by default, and one dial rather than several. What separates the levels is what they
     * cost: reading what the rows already established is free, and finding out which arms they went
     * through means generating a second set of classes and running every row again. A build that did
     * not ask for the second should not pay for it, and a report that quietly measured anyway would
     * make every keystroke in an editor generate bytecode nobody reads.
     */
    public enum Level {
        /** Nothing is measured and nothing is said. */
        OFF,
        /** The cases of the signature, read off rows the compile already ran. */
        WITNESS,
        /** Those, and what the arms and the boundaries took running the rows again to find out. */
        ALL;

        public boolean measuresArms() {
            return this == ALL;
        }

        public boolean reports() {
            return this != OFF;
        }
    }

    /**
     * What a build asked for: how much to measure, and whether to be told it as warnings.
     *
     * <p>Two things rather than one, because a caller can want the measurement without the warnings.
     * {@code souther examples} is that caller — its whole output is the report, which says everything
     * these warnings would say and says it in one place, so printing both would be the same news
     * twice.
     */
    public record Asked(Level level, boolean warn) {

        public static final Asked NOTHING = new Asked(Level.OFF, false);

        /** Measured and said. */
        public static Asked warningsAt(Level level) {
            return new Asked(level, true);
        }

        /** Measured for a report to read, and not said again. */
        public static Asked reportOnly() {
            return reportOnly(Level.ALL);
        }

        /** As much as {@code level} measures, for a report to read. An editor asks for this: what it
         * draws beside a declaration is a report, and a warning saying the same thing again would be
         * the same news twice on the same line. */
        public static Asked reportOnly(Level level) {
            return new Asked(level, false);
        }
    }

    /** What the build asked for. Absent is {@link Asked#NOTHING}. */
    public record Requested() implements Input<Asked> {}

    /** Everything measured about one module, for a caller that wants it in one piece. A map is null
     * where the question could not be answered at all, which is not the same as an empty one. */
    public record Of(Map<String, SignatureEvidence> signatures,
                     Map<String, PartitionEvidence> partitions,
                     Map<String, BranchEvidence> branches) {}

    static Asked askedOf(Db db) {
        Asked asked = db.ask(new Requested()).value();
        return asked == null ? Asked.NOTHING : asked;
    }

    static Level levelOf(Db db) {
        return askedOf(db).level();
    }

    /** What the rows say about one behavior's signature. */
    public record SignatureEvidence(OutputCaseEvidence output, List<InputCaseEvidence> inputs,
                                    MeasurementStatus status) {
        public SignatureEvidence {
            inputs = List.copyOf(inputs);
        }
    }

    /**
     * The signature evidence for every behavior of one module.
     *
     * <p>A module's question, not a source's, although the rows are evaluated per source. A behavior's
     * rows are written across the module's own file and any number of attached {@code examples for}
     * files, so asking this of one source at a time would report the cases the other files cover as
     * uncovered. The per-source answers are read for their values and united here; no row is run twice.
     */
    public record Witnesses(String name) implements Key<Map<String, SignatureEvidence>> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, SignatureEvidence>> compute(Db db) {
            Answer<Ast.Module> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            Answer<Map<String, Sig>> sigs = db.ask(new Bodies.Signatures(name));
            if (!prepared.present() || !scope.present() || !sigs.present()) {
                return Answer.absent();
            }
            Map<String, Observed> byTarget = rowsOf(db, name);
            Map<String, SignatureEvidence> out = new LinkedHashMap<>();
            for (Ast.BehaviorDef behavior : prepared.value().behaviors()) {
                Sig sig = sigs.value().get(behavior.name());
                if (sig == null) {
                    continue;   // a behavior whose signature did not work out has nothing to measure
                }
                out.put(behavior.name(), evidenceOf(sig, scope.value(),
                        byTarget.getOrDefault(behavior.name(), Observed.NONE)));
            }
            return Answer.of(Map.copyOf(out));
        }

    }

    /**
     * What every behavior of one module reaches of the distinctions its model draws.
     *
     * <p>A module's question for the same reason the witnesses are: a behavior's rows are written
     * across its own source and any attached files, and a class covered in one of them is covered.
     */
    public record Coverage(String name) implements Key<Map<String, PartitionEvidence>> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, PartitionEvidence>> compute(Db db) {
            Answer<Ast.Module> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            Answer<Map<String, Sig>> sigs = db.ask(new Bodies.Signatures(name));
            if (!prepared.present() || !scope.present() || !sigs.present()) {
                return Answer.absent();
            }
            souther.compiler.check.TypeChecker.Checked checked =
                    db.ask(new Bodies.Checked(name)).value();
            Map<String, souther.compiler.core.Core> bodies =
                    checked == null ? Map.of() : checked.behaviorBodies();
            souther.compiler.coverage.CoverageSites.Plan plan =
                    souther.compiler.coverage.CoverageSites.of(sourceIdOf(db, name), bodies);
            Map<String, Observed> byTarget = rowsOf(db, name);
            // Whether a guard's boundary can be decided at all: meeting it takes the comparison having
            // been evaluated, which only the instrumented classes say, and only a build that asked
            // for that has them.
            boolean armsMeasured = levelOf(db).measuresArms()
                    && db.ask(new Output.Probed(name)).value() != null;

            Map<String, PartitionEvidence> out = new LinkedHashMap<>();
            for (Ast.BehaviorDef behavior : prepared.value().behaviors()) {
                if (!(behavior instanceof Ast.SpecBehavior spec)) {
                    continue;   // a composition's inputs are its first stage's, measured there
                }
                Sig sig = sigs.value().get(spec.name());
                if (sig == null) {
                    continue;
                }
                out.put(spec.name(), Coverages.of(spec, sig, scope.value(), bodies.get(spec.name()),
                        plan, byTarget.getOrDefault(spec.name(), Observed.NONE), armsMeasured));
            }
            return Answer.of(Map.copyOf(out));
        }

        private static String sourceIdOf(Db db, String module) {
            Front.Layout.Of layout = db.ask(new Front.Layout()).value();
            return layout == null ? module : layout.idOfModule().getOrDefault(module, module);
        }

    }

    /**
     * The rows of one source, run against classes that record the arms they went through.
     *
     * <p>Its own key rather than a mode on {@link Output.Examples}, because what a compile does with
     * rows and what a measurement does with them are different questions asked at different times.
     * Widening the compile's key would put instrumented bytecode into every build, where it changes the
     * time budget a row runs under and the classes a row's constructions initialise — for the benefit
     * of a report that build was not asked for.
     *
     * <p>Every adequacy measure reads these, not the compile's. Two sets of row outcomes for one model
     * can disagree — a row that timed out under one and held under the other — and a report built half
     * from each would say a case is verified and its branch unreached in the same breath. Where they do
     * disagree, that is recorded rather than resolved: which of them is right is not this key's to say.
     */
    public record ProbedExamples(String name, String sourceId) implements Key<Output.Examples.Of> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public String sourceId() {
            return sourceId;
        }

        @Override
        public Answer<Output.Examples.Of> compute(Db db) {
            Map<String, byte[]> probed = levelOf(db).measuresArms()
                    ? db.ask(new Output.ProbedLinked(name)).value() : null;
            if (probed == null) {
                // Nothing was measured, which is not the same as nothing being reached. The rows the
                // compile already ran are what the other measures read; the branch measure says it
                // could not be made.
                return db.ask(new Output.Examples(name, sourceId));
            }
            return Output.Examples.evaluate(db, name, sourceId, probed);
        }
    }

    /**
     * Which arms of each behavior's body the rows go through.
     *
     * <p>Branch-<em>arm</em> coverage, and nothing larger. Going through both arms of two nested
     * conditions is four arms and says nothing about whether their combinations were tried, so nothing
     * here calls this covering the paths a body has.
     *
     * @param all     every arm the behavior has
     * @param covered the ones a row went through
     */
    public record BranchEvidence(List<souther.compiler.coverage.CoverageSites.Site> all,
                                 Set<Integer> covered, MeasurementStatus status) {

        public static final BranchEvidence UNAVAILABLE =
                new BranchEvidence(List.of(), Set.of(), MeasurementStatus.UNAVAILABLE);

        public BranchEvidence {
            all = List.copyOf(all);
            covered = Set.copyOf(covered);
        }

        public List<souther.compiler.coverage.CoverageSites.Site> unreached() {
            return all.stream().filter(site -> !covered.contains(site.index())).toList();
        }
    }

    /**
     * The arms every behavior of one module has, and which of them the rows reach.
     *
     * <p>A hit belongs to the behavior whose arm it is, whichever behavior's row lit it: a row about
     * {@code A} that calls {@code B} did go through {@code B}'s arm, and pretending otherwise would
     * report an arm as unreached that runs on every build. What is <em>not</em> inherited is the
     * question: a behavior nobody wrote a row for is not asked about its unreached arms at all. The
     * measurement is opted into by writing a row, and reaching a behavior sideways is not opting in.
     */
    public record BranchCoverage(String name) implements Key<Map<String, BranchEvidence>> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, BranchEvidence>> compute(Db db) {
            Answer<Ast.Module> prepared = db.ask(new Shapes.Prepared(name));
            if (!prepared.present()) {
                return Answer.absent();
            }
            boolean measured = levelOf(db).measuresArms()
                    && db.ask(new Output.Probed(name)).value() != null;
            souther.compiler.coverage.CoverageSites.Plan plan =
                    souther.compiler.coverage.CoverageSites.Plan.NONE;
            if (measured) {
                plan = Output.Probed.planOf(db, name);
            }
            // A behavior with no `let` has no arms, which is not the same as a body whose arms nothing
            // reaches. The bodies say which is which; the arm count cannot, since a body with no fork
            // in it also has none.
            souther.compiler.check.TypeChecker.Checked checked =
                    db.ask(new Bodies.Checked(name)).value();
            Set<String> withBodies = checked == null ? Set.of() : checked.behaviorBodies().keySet();
            Map<String, Observed> byTarget = rowsOf(db, name);
            Set<Integer> lit = new LinkedHashSet<>();
            for (Observed observed : byTarget.values()) {
                for (RowOutcome row : observed.rows()) {
                    lit.addAll(row.hits());
                }
            }

            Map<String, BranchEvidence> out = new LinkedHashMap<>();
            for (Ast.BehaviorDef behavior : prepared.value().behaviors()) {
                List<souther.compiler.coverage.CoverageSites.Site> arms = plan.sites().stream()
                        .filter(site -> site.behavior().equals(behavior.name())).toList();
                Observed observed = byTarget.getOrDefault(behavior.name(), Observed.NONE);
                if (!measured || !withBodies.contains(behavior.name())
                        || observed.rows().isEmpty()) {
                    // Nothing to measure, or nothing asking. A behavior with no body has no arms; one
                    // no row names has not been opted into the measurement, and reaching it through
                    // somebody else's row is not opting in.
                    out.put(behavior.name(), BranchEvidence.UNAVAILABLE);
                    continue;
                }
                Set<Integer> covered = new LinkedHashSet<>(lit);
                covered.retainAll(arms.stream()
                        .map(souther.compiler.coverage.CoverageSites.Site::index).toList());
                // A row that did not finish went somewhere before it stopped, and what it went through
                // was dropped with it. So the arms it did not light are undecided rather than
                // unreached, and the whole measure says so — the arms that were lit are still lit.
                boolean partial = !observed.complete() || observed.rows().stream()
                        .anyMatch(row -> row.disposition() == Disposition.INCOMPLETE);
                out.put(behavior.name(), new BranchEvidence(arms, covered,
                        partial ? MeasurementStatus.PARTIAL : MeasurementStatus.COMPLETE));
            }
            return Answer.of(Map.copyOf(out));
        }
    }

    /** Every row this module's sources observed, grouped by the behavior it is about, run against the
     * classes that record where they went. */
    /**
     * What a module's sources saw of one behavior: the rows, and what stopped them being seen.
     *
     * <p>Both, and carried together, because a measure that reads only the rows cannot tell a case no
     * row covers from a case a row it never saw covers. The evaluation keeps the two apart on purpose
     * — a source with no runtime to run against contributes no rows and one reason — and an aggregate
     * that kept only the rows would answer as if the reason were nothing.
     *
     * @param rows           what was observed
     * @param incompleteness why what was observed is not all there was
     */
    public record Observed(List<RowOutcome> rows, List<Incompleteness> incompleteness) {

        public static final Observed NONE = new Observed(List.of(), List.of());

        public Observed {
            rows = List.copyOf(rows);
            incompleteness = List.copyOf(incompleteness);
        }

        /** Whether everything there was to see was seen. Only then does an unreached thing mean
         * nothing reaches it, rather than nothing was watching. */
        public boolean complete() {
            return incompleteness.isEmpty();
        }

        /** The status a measure over these rows takes before its own reading is considered. */
        public MeasurementStatus status() {
            return complete() ? MeasurementStatus.COMPLETE : MeasurementStatus.PARTIAL;
        }
    }

    /**
     * Every behavior of one module, with what its sources saw and what stopped them.
     *
     * <p>A reason with no behavior to attach it to — a whole source that could not be evaluated —
     * belongs to all of them: nothing in it was seen, so nothing about any behavior it holds rows for
     * is settled.
     */
    static Map<String, Observed> rowsOf(Db db, String module) {
        List<String> origins = db.ask(new Front.ExampleOrigins(module)).value();
        Map<String, List<RowOutcome>> rows = new LinkedHashMap<>();
        Map<String, List<Incompleteness>> stopped = new LinkedHashMap<>();
        List<Incompleteness> everywhere = new ArrayList<>();
        if (origins == null) {
            return Map.of();
        }
        for (String sourceId : new LinkedHashSet<>(origins)) {
            Output.Examples.Of observed = db.ask(new ProbedExamples(module, sourceId)).value();
            if (observed == null) {
                // The source was not evaluated at all. Which behaviors it wrote rows for is exactly
                // what cannot be read, so it counts against every one of them.
                everywhere.add(Incompleteness.of(Incompleteness.Code.RUNTIME_ABSENT, sourceId));
                continue;
            }
            for (RowOutcome row : observed.rows()) {
                rows.computeIfAbsent(row.target(), _ -> new ArrayList<>()).add(row);
            }
            for (Incompleteness gap : observed.incompleteness()) {
                stopped.computeIfAbsent(gap.subject(), _ -> new ArrayList<>()).add(gap);
            }
        }
        Set<String> named = new LinkedHashSet<>(rows.keySet());
        named.addAll(stopped.keySet());
        Map<String, Observed> out = new LinkedHashMap<>();
        for (String behavior : named) {
            List<Incompleteness> gaps = new ArrayList<>(everywhere);
            gaps.addAll(stopped.getOrDefault(behavior, List.of()));
            out.put(behavior, new Observed(rows.getOrDefault(behavior, List.of()), gaps));
        }
        return new WithFallback(out, everywhere);
    }

    /** The map above, answering for a behavior nothing named with whatever stopped every source. A
     * behavior with no rows of its own is still not measurable where a source went unread. */
    private static final class WithFallback extends java.util.AbstractMap<String, Observed> {

        private final Map<String, Observed> known;
        private final Observed fallback;

        WithFallback(Map<String, Observed> known, List<Incompleteness> everywhere) {
            this.known = known;
            this.fallback = everywhere.isEmpty() ? Observed.NONE
                    : new Observed(List.of(), everywhere);
        }

        @Override
        public Observed get(Object key) {
            Observed there = known.get(key);
            return there != null ? there : fallback;
        }

        @Override
        public Observed getOrDefault(Object key, Observed absent) {
            Observed there = known.get(key);
            return there != null ? there : (fallback.complete() ? absent : fallback);
        }

        @Override
        public Set<Entry<String, Observed>> entrySet() {
            return known.entrySet();
        }
    }

    /**
     * Rows that would fill what every behavior of one module has not covered.
     *
     * <p>Its own key rather than part of the coverage, because it costs what the coverage does not: it
     * builds values through the derived decoders to find out which of them a model admits. A report
     * nobody asked to generate rows for should not pay for that.
     *
     * <p>The two kinds of row stay apart in the answer. Filling a combination and writing a row at an
     * edge are different requests, asked with different flags, and a caller that merged them could not
     * take one without the other.
     */
    public record Filling(Generator.GenerationResult pairs, Generator.GenerationResult boundaries) {

        public static final Filling NONE =
                new Filling(Generator.GenerationResult.NONE, Generator.GenerationResult.NONE);

        static Filling stopped(Incompleteness why) {
            return new Filling(new Generator.GenerationResult(List.of(), List.of(), List.of(why)),
                    Generator.GenerationResult.NONE);
        }
    }

    public record Generated(String name) implements Key<Map<String, Filling>> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, Filling>> compute(Db db) {
            Answer<Ast.Module> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            Answer<Map<String, Sig>> sigs = db.ask(new Bodies.Signatures(name));
            if (!prepared.present() || !scope.present() || !sigs.present()) {
                return Answer.absent();
            }
            souther.compiler.check.TypeChecker.Checked checked =
                    db.ask(new Bodies.Checked(name)).value();
            Map<String, souther.compiler.core.Core> bodies =
                    checked == null ? Map.of() : checked.behaviorBodies();
            souther.compiler.coverage.CoverageSites.Plan plan =
                    souther.compiler.coverage.CoverageSites.of(
                            Coverage.sourceIdOf(db, name), bodies);
            Map<String, Observed> byTarget = rowsOf(db, name);
            Symbols symbols = scope.value();

            Map<String, Filling> out = new LinkedHashMap<>();
            ExampleVerifier.Construction building =
                    constructing(db, name, prepared.value(), symbols, sigs.value());
            for (Ast.BehaviorDef behavior : prepared.value().behaviors()) {
                if (!(behavior instanceof Ast.SpecBehavior spec)) {
                    continue;
                }
                Sig sig = sigs.value().get(spec.name());
                if (sig == null) {
                    continue;
                }
                try {
                    out.put(spec.name(), rowsFor(spec, sig, symbols, bodies.get(spec.name()), plan,
                            byTarget.getOrDefault(spec.name(), Observed.NONE), building));
                } catch (LinkageError _) {
                    // The runtime is not on this host's classpath, so nothing can be built to find out
                    // what a model admits. Saying so is not the same as saying the combinations are
                    // impossible, so none of them is reported as one.
                    out.put(spec.name(), Filling.stopped(Incompleteness.of(
                            Incompleteness.Code.RUNTIME_ABSENT, spec.name())));
                }
            }
            return Answer.of(Map.copyOf(out));
        }

        /** A way to build values against this module's own classes, or nothing where there are none to
         * build against. */
        private static ExampleVerifier.Construction constructing(
                Db db, String module, Ast.Module written, Symbols symbols, Map<String, Sig> sigs) {
            Map<String, byte[]> classes = db.ask(new Output.Linked(module)).value();
            Map<String, List<BehaviorRequirement>> requirements =
                    db.ask(new Bodies.Requirements(module)).value();
            if (classes == null || requirements == null) {
                return null;
            }
            Map<String, Ast.FnDef> values = db.ask(new Bodies.Helpers(module)).value();
            return ExampleVerifier.constructing(written, symbols, sigs, classes, requirements,
                    Output.loader(db, Map.of()), values == null ? Map.of() : values);
        }

        private static Filling rowsFor(
                Ast.SpecBehavior spec, Sig sig, Symbols symbols, souther.compiler.core.Core body,
                souther.compiler.coverage.CoverageSites.Plan plan, Observed observed,
                ExampleVerifier.Construction building) {
            List<RowOutcome> rows = observed.rows();
            List<String> parameters = spec.params().stream().map(Ast.Param::name).toList();
            souther.compiler.partition.Partitions.Partitioning partitioning =
                    Coverages.partitioningOf(spec, sig, symbols, body, plan);
            Generator.Subject subject = new Generator.Subject(parameters, sig.ins(),
                    partitioning.axes(), symbols);
            Generator.CandidateCheck check = building == null ? Generator.CandidateCheck.ANY
                    : (at, candidate) -> building.refuse(sig.ins().get(at), candidate.value());

            List<Map<AxisId, Classification>> existing = rows.stream()
                    .map(row -> RowClasses.of(row, parameters, partitioning.axes())).toList();
            Generator.GenerationResult pairs = Generator.fill(subject, existing, check);

            List<BoundaryObligation> unmet = new ArrayList<>();
            for (Axis axis : partitioning.axes()) {
                unmet.addAll(Coverages.unmet(axis, parameters, rows, symbols));
            }
            return new Filling(pairs, Generator.forBoundaries(subject, unmet, check));
        }
    }

    /**
     * What a build asked to be told, as warnings on the declarations they are about.
     *
     * <p>Only what a person can act on. A position the model draws no line through is named in the
     * report and is not a warning: 398 of them across the corpus this was measured on, and every one
     * of them says "no rule was written here", which is a fact about the model and not a mistake in
     * it. A row waiting for a {@code let} is not one either — waiting is the normal state of a model
     * being written.
     *
     * <p>A gap is reported only where the measurement was complete. An undecided one — a row whose
     * value could not be read — is a fact about the reading, and telling an author to write a row
     * they may already have written is worse than saying nothing.
     */
    public record Warnings(String name) implements Key<Boolean> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Boolean> compute(Db db) {
            Asked asked = askedOf(db);
            Level level = asked.level();
            if (!asked.warn() || !level.reports()) {
                return Answer.of(true);
            }
            Answer<Ast.Module> prepared = db.ask(new Shapes.Prepared(name));
            if (!prepared.present()) {
                return Answer.absent();
            }
            Map<String, SignatureEvidence> signatures = db.ask(new Witnesses(name)).value();
            Map<String, PartitionEvidence> partitions =
                    level.measuresArms() ? db.ask(new Coverage(name)).value() : null;
            Map<String, BranchEvidence> branches =
                    level.measuresArms() ? db.ask(new BranchCoverage(name)).value() : null;

            List<Report> reports = new ArrayList<>();
            for (Ast.BehaviorDef behavior : prepared.value().behaviors()) {
                SignatureEvidence signature =
                        signatures == null ? null : signatures.get(behavior.name());
                signatureGaps(behavior, signature, reports);
                if (partitions != null) {
                    boundaryGaps(behavior, partitions.get(behavior.name()), reports);
                }
                if (branches != null) {
                    armGaps(branches.get(behavior.name()), reports);
                }
            }
            return Answer.of(true, reports);
        }

        /** A case of the signature no row says anything about, on the declaration that owes it. */
        private static void signatureGaps(Ast.BehaviorDef behavior, SignatureEvidence signature,
                                          List<Report> reports) {
            if (signature == null || signature.status() != MeasurementStatus.COMPLETE) {
                return;
            }
            for (TypeName missing : signature.output().unspecified()) {
                reports.add(warning("E1913", "check.example.witness.out",
                        "check.example.witness.out.hint", List.of(missing.name()), behavior,
                        missing.name(), behavior.name()));
            }
            for (int i = 0; i < signature.inputs().size(); i++) {
                for (TypeName missing : signature.inputs().get(i).unspecified()) {
                    reports.add(warning("E1915", "check.example.witness.in", null, List.of(),
                            behavior, missing.name(), i + 1, behavior.name()));
                }
            }
        }

        private static void boundaryGaps(Ast.BehaviorDef behavior, PartitionEvidence partition,
                                         List<Report> reports) {
            if (partition == null) {
                return;
            }
            for (PartitionEvidence.BoundaryCoverage boundary : partition.boundaries()) {
                if (boundary.status() == MeasurementStatus.COMPLETE && !boundary.hit()) {
                    reports.add(warning("E1916", "check.example.boundary",
                            "check.example.boundary.hint", List.of(), behavior,
                            boundary.axis(), boundary.value(), boundary.origin()));
                }
            }
        }

        /** An arm no row goes through, quoted at the arm and not at the declaration: what to do about
         * it is written there. */
        private static void armGaps(BranchEvidence branch, List<Report> reports) {
            if (branch == null || branch.status() != MeasurementStatus.COMPLETE) {
                return;
            }
            for (souther.compiler.coverage.CoverageSites.Site arm : branch.unreached()) {
                reports.add(Report.of(souther.compiler.diag.Diagnostic
                        .of("E1918", "check.example.unreachedarm").warning()
                        .title("check.example.title")
                        .at(arm.at().pos())
                        .args(arm.label(), arm.behavior())
                        .hint("check.example.unreachedarm.hint")
                        .build()));
            }
        }

        /**
         * One warning on a behavior's declaration.
         *
         * <p>{@code hint} is null where the message says all there is to say. Written out at the call
         * site rather than derived from the message's key, so that a scan for the keys this names
         * finds them — a key built by concatenation is one nothing can see is used.
         */
        private static Report warning(String code, String key, String hint,
                                      List<Object> hintArgs, Ast.BehaviorDef behavior,
                                      Object... args) {
            souther.compiler.diag.Diagnostic.Builder built =
                    souther.compiler.diag.Diagnostic.of(code, key).warning()
                            .title("check.example.title")
                            .at(behavior.pos())
                            .args(args);
            if (hint != null) {
                built.hint(hint, hintArgs.toArray());
            }
            return Report.of(built.build());
        }
    }

    /**
     * What a behavior's rows establish about its signature.
     *
     * <p>Which set a row lands in is decided by how far it got, never by whether it passed. A row that
     * disagreed still applied the behavior and still saw an answer, and a coverage measure that dropped
     * it would report the case it produced as one nothing produces.
     */
    /**
     * The cases a position has to be covered at, which is not quite what a row's expected arm is held
     * against ({@link TypeOps#outputCases}).
     *
     * <p>A position typed as one data has one case, and covering it is not a question: any row at all
     * covers it, so reporting {@code 1/1} everywhere adds a number that is never anything else. What
     * is worth counting is a position that can be more than one thing. The arm check is wider on
     * purpose — it uses the single name to catch a row that wrote the wrong one.
     */
    private static Set<TypeName> coverableCases(Type t, Symbols symbols) {
        return TypeOps.isSumType(t, symbols) ? TypeOps.leafCases(t, symbols) : Set.of();
    }

    static SignatureEvidence evidenceOf(Sig sig, Symbols symbols, Observed seen) {
        List<RowOutcome> rows = seen.rows();
        Set<TypeName> declaredOut = coverableCases(sig.out(), symbols);
        Set<TypeName> specified = new LinkedHashSet<>();
        Set<TypeName> observed = new LinkedHashSet<>();
        Set<TypeName> verified = new LinkedHashSet<>();
        int unreadableOut = 0;

        List<Type> ins = sig.ins();
        List<Set<TypeName>> declaredIn = new ArrayList<>(ins.size());
        List<Set<TypeName>> inSpecified = new ArrayList<>(ins.size());
        List<Set<TypeName>> inExecuted = new ArrayList<>(ins.size());
        List<Set<TypeName>> inVerified = new ArrayList<>(ins.size());
        int[] unreadableIn = new int[ins.size()];
        for (Type in : ins) {
            declaredIn.add(coverableCases(in, symbols));
            inSpecified.add(new LinkedHashSet<>());
            inExecuted.add(new LinkedHashSet<>());
            inVerified.add(new LinkedHashSet<>());
        }

        for (RowOutcome row : rows) {
            boolean held = row.disposition() == Disposition.HELD;
            if (row.expectedArm() != null) {
                specified.add(row.expectedArm());
            } else if (!declaredOut.isEmpty()) {
                unreadableOut++;   // an expectation whose case the text does not say
            }
            if (row.resultArm() != null) {
                observed.add(row.resultArm());
                if (held) {
                    verified.add(row.resultArm());
                }
            }
            for (int i = 0; i < ins.size(); i++) {
                if (declaredIn.get(i).isEmpty()) {
                    continue;   // not a sum: nothing to cover at this position
                }
                TypeName written = i < row.inputCases().size() ? row.inputCases().get(i) : null;
                if (written == null) {
                    unreadableIn[i]++;
                    continue;
                }
                if (row.stage().reached(Stage.FIXTURES_VALIDATED)) {
                    inSpecified.get(i).add(written);
                }
                if (row.stage().reached(Stage.INVOKED)) {
                    inExecuted.get(i).add(written);
                }
                if (held) {
                    inVerified.get(i).add(written);
                }
            }
        }

        OutputCaseEvidence output = declaredOut.isEmpty() ? OutputCaseEvidence.none()
                : new OutputCaseEvidence(declaredOut, specified, observed, verified, unreadableOut);
        List<InputCaseEvidence> inputs = new ArrayList<>(ins.size());
        boolean partial = output.status() == MeasurementStatus.PARTIAL;
        for (int i = 0; i < ins.size(); i++) {
            InputCaseEvidence evidence = declaredIn.get(i).isEmpty() ? InputCaseEvidence.none()
                    : new InputCaseEvidence(declaredIn.get(i), inSpecified.get(i), inExecuted.get(i),
                            inVerified.get(i), unreadableIn[i]);
            inputs.add(evidence);
            partial |= evidence.status() == MeasurementStatus.PARTIAL;
        }
        // Nothing was measured where nothing was written: a behavior with no rows has no gaps to
        // report, only an absence of evidence, and saying so is not the same as saying it is covered.
        // A source that could not be evaluated is a set of rows nothing has seen, and a case they may
        // have covered reads exactly like a case nothing covers.
        partial |= !seen.complete();
        MeasurementStatus status = rows.isEmpty() && seen.complete()
                ? MeasurementStatus.UNAVAILABLE
                : partial ? MeasurementStatus.PARTIAL : MeasurementStatus.COMPLETE;
        return new SignatureEvidence(output, inputs, status);
    }

    private Adequacy() {}
}
