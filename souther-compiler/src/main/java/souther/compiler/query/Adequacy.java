package souther.compiler.query;


import souther.compiler.diag.DiagnosticCode;
import souther.compiler.diag.SourcePos;
import souther.compiler.ExampleVerifier;
import souther.compiler.FixtureReader;
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
import souther.compiler.partition.Exclusions;
import souther.compiler.partition.Generator;
import souther.compiler.partition.RowClasses;
import souther.compiler.types.Type;
import souther.compiler.types.TypeName;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Optional;
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

    /** Nothing proven and nothing disproved, for a module whose reachability could not be asked. */
    static final Effective NOTHING_PROVEN =
            new Effective(souther.compiler.partition.GuardReachability.NONE, Set.of());

    static Asked askedOf(Db db) {
        Asked asked = db.ask(new Requested()).value();
        return asked == null ? Asked.NOTHING : asked;
    }

    static Level levelOf(Db db) {
        return askedOf(db).level();
    }

    /**
     * What this compilation's rows have to record as they run.
     *
     * <p>Derived from the level rather than being the level, because what changes the bytecode is
     * only whether the arms are wanted. Two levels that want the same thing are then one evaluation,
     * and asking for a wider report does not re-run the rows.
     */
    static Output.CoverageMode coverageAsked(Db db) {
        return levelOf(db).measuresArms() ? Output.CoverageMode.ARMS : Output.CoverageMode.NONE;
    }

    /** What the rows say about one behavior's signature. */
    public record SignatureEvidence(OutputCaseEvidence output, List<InputCaseEvidence> inputs,
                                    MeasurementStatus status, Reason reason) {

        /** Why the signature has no numbers. */
        public enum Reason {
            /** No row names this behavior, so nothing was established about it either way. */
            NO_ROWS
        }

        public static SignatureEvidence unavailable(OutputCaseEvidence output,
                                                    List<InputCaseEvidence> inputs, Reason reason) {
            return new SignatureEvidence(output, inputs, MeasurementStatus.UNAVAILABLE, reason);
        }

        public SignatureEvidence {
            inputs = List.copyOf(inputs);
            Unavailable.check(status, reason);
        }
    }

    /**
     * What each behavior of one module says it does not answer for.
     *
     * <p>Asked once, here, and read by every measure that needs a denominator. The signature's cases,
     * the classes a position is divided into and the rows the generator offers are three counts of the
     * same universe, and deriving what is in it three times is three chances to disagree — which is
     * how a case behind an {@code unreachable} came to be asked for by three measures at once.
     */
    public record Excluded(String name) implements Key<Map<String, Exclusions>> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, Exclusions>> compute(Db db) {
            Answer<Ast.Module> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = db.ask(new Shapes.Scope(name));
            if (!prepared.present() || !scope.present()) {
                return Answer.absent();
            }
            souther.compiler.check.TypeChecker.Checked checked =
                    db.ask(new Bodies.Checked(name)).value();
            Map<String, souther.compiler.core.Core> bodies =
                    checked == null ? Map.of() : checked.behaviorBodies();
            Map<String, Exclusions> out = new LinkedHashMap<>();
            for (Ast.BehaviorDef behavior : prepared.value().behaviors()) {
                if (!(behavior instanceof Ast.SpecBehavior spec)) {
                    continue;   // a composition has no body of its own to read this off
                }
                out.put(spec.name(), Exclusions.of(bodies.get(spec.name()),
                        spec.params().stream().map(Ast.Param::name).toList(), scope.value()));
            }
            return Answer.of(Ordered.map(out));
        }
    }

    /**
     * The arms of every behavior of one module that the model's own rules prove nothing reaches.
     *
     * <p>Asked once, for the same reason {@link Excluded} is: what a position is divided into, which
     * lines are owed a row, which arms are owed a row and which cases the signature is owed are
     * projections of one universe of possible executions. Derived per measure they disagreed — the
     * class beyond a cap was dropped while the arm behind it was still asked for.
     *
     * <p>A guard whose comparison this cannot read leaves both of its arms owed, and so does a position
     * nothing bounds. Only a proof takes an arm away.
     */
    public record Reachable(String name)
            implements Key<Map<String, souther.compiler.partition.GuardReachability>> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, souther.compiler.partition.GuardReachability>> compute(Db db) {
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
            Map<String, Exclusions> excluded = db.ask(new Excluded(name)).value();
            Symbols symbols = scope.value();
            Map<String, souther.compiler.partition.GuardReachability> out = new LinkedHashMap<>();
            for (Ast.BehaviorDef behavior : prepared.value().behaviors()) {
                if (!(behavior instanceof Ast.SpecBehavior spec)) {
                    continue;   // a composition has no body of its own, so no arms of its own
                }
                souther.compiler.core.Core body = bodies.get(spec.name());
                Sig sig = sigs.value().get(spec.name());
                if (body == null || sig == null) {
                    continue;
                }
                List<String> parameters = spec.params().stream().map(Ast.Param::name).toList();
                souther.compiler.partition.GuardThresholds.Guards guards =
                        souther.compiler.partition.GuardThresholds.of(
                                spec.name(), body, plan, parameters, symbols);
                // What the positions can hold, read before any threshold is applied: a guard's own line
                // is not what says whether that line is reachable.
                Map<String, souther.compiler.numeric.NumericDomain.Bounds> admissible =
                        souther.compiler.partition.Partitions.of(spec, sig, symbols,
                                excluded == null ? Exclusions.NONE
                                        : excluded.getOrDefault(spec.name(), Exclusions.NONE))
                                .domains();
                out.put(spec.name(), souther.compiler.partition.GuardReachability.of(
                        guards.edges(), admissible));
            }
            return Answer.of(Ordered.map(out));
        }
    }

    /**
     * What is proven about a behavior's arms once the rows have run.
     *
     * <p>A proof is about the model's own rules and the rows are about what happened, so a row that
     * went through an arm nothing was supposed to reach settles it: the proof was wrong. Recorded
     * rather than dropped, because that is a disagreement between an analysis and an execution and
     * not a gap in anybody's rows.
     *
     * @param reachable  the arms still proven unreachable, which is what every measure excludes by
     * @param contradicted the ones a row reached anyway
     */
    public record Effective(souther.compiler.partition.GuardReachability reachable, Set<Integer> contradicted) {

        public Effective {
            contradicted = Set.copyOf(contradicted);
        }
    }

    /**
     * The effective reachability of every behavior of one module.
     *
     * <p>Derived once and read by both of the measures that exclude by it. Asked separately they
     * would disagree exactly where it matters most: an arm put back into the branch measure by a row
     * that reached it would still be taken out of the signature's, and the case behind it would stay
     * unowed over a proof already known to be wrong.
     */
    public record Reached(String name) implements Key<Map<String, Effective>> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, Effective>> compute(Db db) {
            Answer<Map<String, souther.compiler.partition.GuardReachability>> proven = db.ask(new Reachable(name));
            if (!proven.present()) {
                return Answer.absent();
            }
            Set<Integer> lit = new LinkedHashSet<>();
            for (Observed observed : rowsOf(db, name).values()) {
                for (RowOutcome row : observed.rows()) {
                    lit.addAll(row.hits());
                }
            }
            Map<String, Effective> out = new LinkedHashMap<>();
            proven.value().forEach((behavior, reachable) -> {
                Set<Integer> contradicted = new LinkedHashSet<>(reachable.unreachableSites());
                contradicted.retainAll(lit);
                out.put(behavior, new Effective(reachable.without(contradicted), contradicted));
            });
            return Answer.of(Ordered.map(out));
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
            Map<String, Exclusions> excluded = db.ask(new Excluded(name)).value();
            // What each body can answer with, so that a case only an unreachable arm produces is not
            // counted. Read from the same reachability the arms are counted by.
            souther.compiler.check.TypeChecker.Checked checkedBodies =
                    db.ask(new Bodies.Checked(name)).value();
            Map<String, souther.compiler.core.Core> producing =
                    checkedBodies == null ? Map.of() : checkedBodies.behaviorBodies();
            souther.compiler.coverage.CoverageSites.Plan producingPlan =
                    souther.compiler.coverage.CoverageSites.of(
                            Coverage.sourceIdOf(db, name), producing);
            Map<String, Effective> reachableArms = db.ask(new Reached(name)).value();
            Map<String, SignatureEvidence> out = new LinkedHashMap<>();
            for (Ast.BehaviorDef behavior : prepared.value().behaviors()) {
                Sig sig = sigs.value().get(behavior.name());
                if (sig == null) {
                    continue;   // a behavior whose signature did not work out has nothing to measure
                }
                out.put(behavior.name(), evidenceOf(sig, scope.value(),
                        byTarget.getOrDefault(behavior.name(), Observed.NONE),
                        behavior instanceof Ast.SpecBehavior spec ? spec.params().stream()
                                .map(Ast.Param::name).toList() : List.of(),
                        excluded == null ? Exclusions.NONE
                                : excluded.getOrDefault(behavior.name(), Exclusions.NONE),
                        producing.get(behavior.name()), producingPlan,
                        reachableArms == null ? NOTHING_PROVEN
                                : reachableArms.getOrDefault(behavior.name(), NOTHING_PROVEN)));
            }
            return Answer.of(Ordered.map(out));
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
            Map<String, Exclusions> excluded = db.ask(new Excluded(name)).value();
            // What every line this module's rules drew came to, asked once and read here. Measuring a
            // line takes building values, which is not this measure's work and not work to do twice.
            Map<String, List<BoundaryAssessment>> boundaries = db.ask(new Boundaries(name)).value();

            Map<String, PartitionEvidence> out = new LinkedHashMap<>();
            for (Ast.BehaviorDef behavior : prepared.value().behaviors()) {
                if (!(behavior instanceof Ast.SpecBehavior spec)) {
                    continue;   // a composition's inputs are its first stage's, measured there
                }
                Sig sig = sigs.value().get(spec.name());
                if (sig == null) {
                    continue;
                }
                Observed seen = byTarget.getOrDefault(spec.name(), Observed.NONE);
                out.put(spec.name(), Coverages.of(spec, sig, scope.value(), bodies.get(spec.name()),
                        plan, seen,
                        boundaries == null ? List.of()
                                : boundaries.getOrDefault(spec.name(), List.of()),
                        excluded == null ? Exclusions.NONE
                                : excluded.getOrDefault(spec.name(), Exclusions.NONE)));
            }
            return Answer.of(Ordered.map(out));
        }

        private static String sourceIdOf(Db db, String module) {
            Front.Layout.Of layout = db.ask(new Front.Layout()).value();
            return layout == null ? module : layout.idOfModule().getOrDefault(module, module);
        }

    }

    /**
     * What is known about every line each behavior's rules drew.
     *
     * <p>The one authority on a boundary. Whether a row sits at it and whether a row could sit at it
     * were established in two places under two sets of rules — the report read one, the generator read
     * the other — and the two disagreed about the same line: a boundary the report declined to name
     * because a row had gone unread was one the generator handed to an author anyway, and a boundary
     * the projection could not promise was one the generator had already built a value for and thrown
     * the answer away.
     *
     * <p>Its own key rather than part of the coverage, because it costs what a coverage count does not:
     * it puts values through this module's own decoders. Not behind the flag that prints rows, though.
     * Whether a value can be built is evidence, and whether an author is handed the row that proves it
     * is a separate request — the first decides what the report may count, so tying it to the second
     * would make one measure's number depend on another flag.
     */
    public record Boundaries(String name) implements Key<Map<String, List<BoundaryAssessment>>> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, List<BoundaryAssessment>>> compute(Db db) {
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
            Map<String, Exclusions> excluded = db.ask(new Excluded(name)).value();
            Symbols symbols = scope.value();
            // Whether a guard's boundary can be decided at all: meeting it takes the comparison having
            // been evaluated, which only the instrumented classes say.
            boolean armsAsked = levelOf(db).measuresArms();
            FixtureReader.Construction building = constructing(db, name, prepared.value(), symbols);

            Map<String, List<BoundaryAssessment>> out = new LinkedHashMap<>();
            for (Ast.BehaviorDef behavior : prepared.value().behaviors()) {
                if (!(behavior instanceof Ast.SpecBehavior spec)) {
                    continue;   // a composition's inputs are its first stage's, measured there
                }
                Sig sig = sigs.value().get(spec.name());
                if (sig == null) {
                    continue;
                }
                out.put(spec.name(), assess(spec, sig, symbols, bodies.get(spec.name()), plan,
                        byTarget.getOrDefault(spec.name(), Observed.NONE), armsAsked, building,
                        excluded == null ? Exclusions.NONE
                                : excluded.getOrDefault(spec.name(), Exclusions.NONE)));
            }
            return Answer.of(Ordered.map(out));
        }

        /** Every line of one behavior, with what the rows and the decoder say about each. */
        private static List<BoundaryAssessment> assess(
                Ast.SpecBehavior spec, Sig sig, Symbols symbols, souther.compiler.core.Core body,
                souther.compiler.coverage.CoverageSites.Plan plan, Observed observed,
                boolean armsAsked, FixtureReader.Construction building, Exclusions excluded) {
            List<String> parameters = spec.params().stream().map(Ast.Param::name).toList();
            souther.compiler.partition.Partitions.Partitioning partitioning =
                    Coverages.partitioningOf(spec, sig, symbols, body, plan, excluded);
            Coverages.Probe probe = probing(partitioning, sig, symbols, parameters, building);
            List<BoundaryAssessment> out = new ArrayList<>();
            for (Axis axis : partitioning.axes()) {
                if (!axis.measurable()) {
                    continue;
                }
                out.addAll(Coverages.assess(axis, parameters, observed, symbols, armsAsked,
                        partitioning.edgeIsKnownWritable(axis.path().toString()), probe,
                        partitioning.domains().get(axis.path().toString())));
            }
            return List.copyOf(out);
        }

        /**
         * A way to try to build a row at a boundary, or nothing where there is nothing to try against.
         *
         * <p>Nothing rather than a check that refuses nothing. A row built without the decoder is a row
         * nobody has put through anything, and counting one as a witness would turn "the classes are
         * missing" into "the edge can be written".
         */
        private static Coverages.Probe probing(
                souther.compiler.partition.Partitions.Partitioning partitioning, Sig sig,
                Symbols symbols, List<String> parameters, FixtureReader.Construction building) {
            if (building == null) {
                return null;
            }
            Generator.Subject subject = new Generator.Subject(parameters, sig.inputTypes(),
                    partitioning.axes(), symbols);
            Generator.CandidateCheck check =
                    (at, candidate) -> building.refuse(sig.ins().get(at), candidate.value());
            return obligation -> {
                try {
                    return Generator.probe(subject, obligation, check);
                } catch (LinkageError _) {
                    // The generated classes would not link, so nothing can be built to find out
                    // what a model admits. Nothing was tried, which is not the same as everything
                    // tried being refused, and neither of them says the edge cannot be written.
                    return null;
                }
            };
        }
    }


    /**
     * Which arms of each behavior's body the rows go through.
     *
     * <p>Branch-<em>arm</em> coverage, and nothing larger. Going through both arms of two nested
     * conditions is four arms and says nothing about whether their combinations were tried, so nothing
     * here calls this covering the paths a body has.
     *
     * @param all     every arm the behavior is owed a row for. An arm the model's own rules prove
     *                nothing reaches is not one of them: it is instrumented, because a probe is what
     *                would show the proof wrong, and it is not owed, because no row can light it.
     *                Which arms those are is {@link GuardReachability}'s answer, asked once for the
     *                module and read by every measure.
     * @param covered the ones a row went through
     * @param contradicted arms proven unreachable that a row went through anyway. Nothing in the model
     *                is wrong here — the proof is. Kept rather than dropped, and the arm is left in
     *                {@link #all} beside it, because a measure that quietly counted such an arm as
     *                covered would report a full denominator and hide the one fact worth acting on.
     */
    public record BranchEvidence(List<souther.compiler.coverage.CoverageSites.Site> all,
                                 Set<Integer> covered, Set<Integer> contradicted,
                                 MeasurementStatus status, Reason reason) {

        /**
         * Why a behavior's arms have no number, in the order the measurement asks.
         *
         * <p>The first gate that did not open is the answer. They are asked in that order because that
         * is the order the work happens in: a body has to exist before anything can be asked about it,
         * the build has to ask before the classes are generated, the classes have to survive before a
         * row can carry what it went through, and a row has to name the behavior before any of it is
         * about this one.
         */
        public enum Reason {
            /** A {@code >->} composition or a behavior with no {@code let}. It has no arms of its own,
             *  so the measure does not apply rather than failing. */
            NO_BODY,
            /** The build did not ask for the arms, which cost a second run of every row. */
            NOT_ASKED,
            /** The rows ran without instrumentation, so what they went through went with it. */
            UNREADABLE,
            /** No row names this behavior. The measurement is opted into by writing one, and reaching
             *  the behavior through somebody else's row is not opting in. */
            NO_ROWS
        }

        public static BranchEvidence unavailable(Reason reason) {
            return new BranchEvidence(List.of(), Set.of(), Set.of(),
                    MeasurementStatus.UNAVAILABLE, reason);
        }

        /**
         * The arms of one behavior, with the ones nothing reaches taken out of what it is owed.
         *
         * <p>Taken out here and not where the probes are numbered. The plan says where instrumentation
         * is; this says which of it is owed a row, and the two are different questions — a site with no
         * probe could never disprove the reachability it was excluded by.
         */
        public static BranchEvidence measured(List<souther.compiler.coverage.CoverageSites.Site> all,
                                              Set<Integer> covered, Effective reachable,
                                              MeasurementStatus status) {
            List<souther.compiler.coverage.CoverageSites.Site> owed = all.stream()
                    .filter(site -> !reachable.reachable().provenUnreachable(site.index())).toList();
            Set<Integer> counted = new LinkedHashSet<>(covered);
            counted.retainAll(owed.stream()
                    .map(souther.compiler.coverage.CoverageSites.Site::index).toList());
            // A proof a row has already disproved is not something to report a complete measurement
            // over. What is wrong is this analysis, not the model's rows, and a number given as though
            // nothing had happened is the one thing that must not come out of it.
            return new BranchEvidence(owed, counted, reachable.contradicted(),
                    reachable.contradicted().isEmpty() ? status : MeasurementStatus.PARTIAL, null);
        }

        public BranchEvidence {
            all = List.copyOf(all);
            covered = Set.copyOf(covered);
            contradicted = Set.copyOf(contradicted);
            Unavailable.check(status, reason);
        }

        /**
         * Whether this behavior has arms for the measure to be about.
         *
         * <p>Asked instead of reading {@link Reason#NO_BODY} at each caller. Having nothing to measure
         * is not the same as failing to measure, and {@link MeasurementStatus} has no word for the
         * first; {@code NO_BODY} is where that distinction is kept until it does. A caller that read
         * the constant would be holding the encoding rather than the question.
         */
        public boolean applicable() {
            return reason != Reason.NO_BODY;
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
            boolean measured = levelOf(db).measuresArms();
            souther.compiler.coverage.CoverageSites.Plan plan =
                    souther.compiler.coverage.CoverageSites.Plan.NONE;
            if (measured) {
                plan = Output.Evaluated.planOf(db, name);
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

            Map<String, Effective> reachable = db.ask(new Reached(name)).value();

            Map<String, BranchEvidence> out = new LinkedHashMap<>();
            for (Ast.BehaviorDef behavior : prepared.value().behaviors()) {
                List<souther.compiler.coverage.CoverageSites.Site> arms = plan.sites().stream()
                        .filter(site -> site.behavior().equals(behavior.name())).toList();
                Observed observed = byTarget.getOrDefault(behavior.name(), Observed.NONE);
                BranchEvidence.Reason absent =
                        whyNoArms(behavior.name(), withBodies, measured, observed);
                if (absent != null) {
                    out.put(behavior.name(), BranchEvidence.unavailable(absent));
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
                out.put(behavior.name(), BranchEvidence.measured(arms, covered,
                        reachable == null ? NOTHING_PROVEN
                                : reachable.getOrDefault(behavior.name(), NOTHING_PROVEN),
                        partial ? MeasurementStatus.PARTIAL : MeasurementStatus.COMPLETE));
            }
            return Answer.of(Ordered.map(out));
        }

        /**
         * The first gate the arm measurement did not get through, or null where it got through them
         * all.
         *
         * <p>One gate per condition, in the order the work happens in, so that what a caller reads back
         * is the thing that stopped it rather than whichever condition an expression happened to test
         * first. The bodies say which behaviors have arms; the arm count cannot, since a body with no
         * fork in it also has none.
         */
        private static BranchEvidence.Reason whyNoArms(String behavior, Set<String> withBodies,
                                                       boolean measured, Observed observed) {
            if (!withBodies.contains(behavior)) {
                return BranchEvidence.Reason.NO_BODY;
            }
            if (!measured) {
                return BranchEvidence.Reason.NOT_ASKED;
            }
            if (observed.armsUnseen()) {
                return BranchEvidence.Reason.UNREADABLE;
            }
            // Nothing read is not the same as nothing written. Where a source could not be evaluated
            // at all, the rows this behavior is waiting on may be sitting in it, and answering
            // `NO_ROWS` would tell an author to write what is already there. The measure goes ahead
            // on what was seen and comes back undecided, which is what it is.
            if (observed.rows().isEmpty() && !observed.someRowsUnseen()) {
                return BranchEvidence.Reason.NO_ROWS;
            }
            return null;
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

        /**
         * Whether the arms were asked for and not produced.
         *
         * <p>The rows below then ran without instrumentation and carry no arms at all, which reads
         * exactly like a body no row goes through. Not the same as arms nobody asked for.
         */
        public boolean armsUnseen() {
            return incompleteness.stream()
                    .anyMatch(gap -> gap.code() == Incompleteness.Code.INSTRUMENTATION_ABSENT);
        }

        /**
         * Whether some rows were never seen at all, as against seen and not finished.
         *
         * <p>The difference decides who has to notice. A row that ran out of time is here, and says
         * so: its state is dropped rather than read, so it arrives with no inputs and no expected arm
         * and every measure that reads a row finds one it cannot place. A source that could not be
         * evaluated leaves no row to find — the rows it holds may cover anything, and a measure over
         * the rows that remain is a measure over some of them with nothing in it to say so.
         *
         * <p>Two codes say it, and they are the two ways rows go unobserved: a source that produced
         * no observation at all, and an example block whose classes would not load. What this asks is
         * the state and not the cause, so it reads both rather than one standing in for the other —
         * which is what it did while one code carried them both.
         */
        public boolean someRowsUnseen() {
            return incompleteness.stream()
                    .anyMatch(gap -> gap.code() == Incompleteness.Code.OBSERVATION_ABSENT
                            || gap.code() == Incompleteness.Code.LINKAGE_FAILED);
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
            Output.Examples.Of observed = db.ask(Output.Examples.asked(db, module, sourceId)).value();
            if (observed == null) {
                // The source was not evaluated at all. Which behaviors it wrote rows for is exactly
                // what cannot be read, so it counts against every one of them.
                everywhere.add(Incompleteness.of(Incompleteness.Code.OBSERVATION_ABSENT,
                        Incompleteness.Scope.SOURCE, sourceId));
                continue;
            }
            for (RowOutcome row : observed.rows()) {
                rows.computeIfAbsent(row.target(), _ -> new ArrayList<>()).add(row);
            }
            for (Incompleteness gap : observed.incompleteness()) {
                Optional<String> one = gap.behavior();
                if (one.isPresent()) {
                    stopped.computeIfAbsent(one.get(), _ -> new ArrayList<>()).add(gap);
                } else {
                    everywhere.add(gap);   // larger than a behavior, so about all of them
                }
            }
        }
        everywhere = distinct(everywhere);
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

    /** One entry per reason. A module's classes failing to be instrumented is one fact, and looking
     * for them once per source is not three facts. */
    private static List<Incompleteness> distinct(List<Incompleteness> gaps) {
        Map<Object, Incompleteness> byIdentity = new LinkedHashMap<>();
        for (Incompleteness gap : gaps) {
            byIdentity.putIfAbsent(gap.identity(), gap);
        }
        return List.copyOf(byIdentity.values());
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
     * <p>Its own key rather than part of the coverage, because filling the combinations searches the
     * pair space, which nobody who only wanted a report should pay for. The rows at the edges are not
     * that: {@link Boundaries} builds one value per line to find out whether a line can be written at,
     * and the row that comes of it is read from there rather than searched for again.
     *
     * <p>The two kinds of row stay apart in the answer. Filling a combination and writing a row at an
     * edge are different requests, asked with different flags, and a caller that merged them could not
     * take one without the other.
     */
    public record Filling(Generator.GenerationResult pairs, Generator.GenerationResult boundaries) {

        public static final Filling NONE =
                new Filling(Generator.GenerationResult.NONE, Generator.GenerationResult.NONE);

        static Filling stopped(souther.compiler.partition.GenerationReason why) {
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
            Map<String, Exclusions> excluded = db.ask(new Excluded(name)).value();
            Symbols symbols = scope.value();

            Map<String, List<BoundaryAssessment>> boundaries =
                    db.ask(new Boundaries(name)).value();

            Map<String, Filling> out = new LinkedHashMap<>();
            FixtureReader.Construction building = constructing(db, name, prepared.value(), symbols);
            for (Ast.BehaviorDef behavior : prepared.value().behaviors()) {
                if (!(behavior instanceof Ast.SpecBehavior spec)) {
                    continue;
                }
                Sig sig = sigs.value().get(spec.name());
                if (sig == null) {
                    continue;
                }
                Generator.GenerationResult atEdges = offered(spec.name(),
                        boundaries == null ? List.of()
                                : boundaries.getOrDefault(spec.name(), List.of()));
                try {
                    out.put(spec.name(), new Filling(pairsFor(spec, sig, symbols,
                            bodies.get(spec.name()), plan,
                            byTarget.getOrDefault(spec.name(), Observed.NONE), building,
                            excluded == null ? Exclusions.NONE
                                    : excluded.getOrDefault(spec.name(), Exclusions.NONE)),
                            atEdges));
                } catch (LinkageError _) {
                    // The generated classes would not link, so nothing can be built to find out
                    // what a model admits. Saying so is not the same as saying the combinations are
                    // impossible, so none of them is reported as one.
                    out.put(spec.name(), Filling.stopped(
                            new souther.compiler.partition.GenerationReason.ClassesWouldNotLink(
                                    spec.name())));
                }
            }
            // In the order the module declares them, because the block printed from this is read
            // against the one before it.
            return Answer.of(Ordered.map(out));
        }

        /**
         * The rows at the edges, read off what the boundary assessment already tried.
         *
         * <p>Nothing is built here, and nothing is worked out from the verdict either. The attempt
         * says what happened; this prints it. Reading it back off {@link BoundaryAssessment#writability()}
         * would lose the case that matters most to an author — an edge the projection proves is
         * writable and the search could not produce a row for — which came out as a verdict of
         * "provable" with nothing said about the row that never appeared.
         */
        private static Generator.GenerationResult offered(String behavior,
                                                          List<BoundaryAssessment> boundaries) {
            List<Generator.GeneratedRow> rows = new ArrayList<>();
            List<Generator.UnresolvedCombination> unresolved = new ArrayList<>();
            List<souther.compiler.partition.GenerationReason> stopped = new ArrayList<>();
            for (BoundaryAssessment each : boundaries) {
                switch (each.attempt()) {
                    case BoundaryAssessment.Attempt.Built built -> rows.add(built.row());
                    case BoundaryAssessment.Attempt.Unresolved why -> unresolved.add(why.why());
                    // Nothing was tried. One of the reasons is news — the decoders could not be
                    // reached, so this block is short of rows it would otherwise have offered — and
                    // two are boundaries nobody is owed a row at, where saying so would be noise.
                    //
                    // NO_CLASSES is here for completeness and does not arrive: the evaluation is
                    // asked only of a module that checked, so a module with no classes has no rows
                    // either, and a boundary with no rows behind it is undecided rather than missed.
                    // Reaching it takes the backend failing on a module that checked, which is a
                    // defect in the backend rather than a state of the source. It says the same
                    // thing as the reason beside it — nothing could be built against — and that is
                    // what is said.
                    case BoundaryAssessment.Attempt.NotAttempted absent -> {
                        if (absent.reason() == BoundaryAssessment.Attempt.Reason.LINKAGE_FAILED
                                || absent.reason()
                                        == BoundaryAssessment.Attempt.Reason.NO_CLASSES) {
                            stopped.add(new souther.compiler.partition.GenerationReason
                                    .ClassesWouldNotLink(behavior));
                        }
                    }
                }
            }
            return new Generator.GenerationResult(rows, unresolved,
                    stopped.stream().distinct().toList());
        }

        private static Generator.GenerationResult pairsFor(
                Ast.SpecBehavior spec, Sig sig, Symbols symbols, souther.compiler.core.Core body,
                souther.compiler.coverage.CoverageSites.Plan plan, Observed observed,
                FixtureReader.Construction building, Exclusions excluded) {
            if (observed.someRowsUnseen()) {
                // Rows exist that nothing read. What they cover is unknown, so what is left uncovered
                // is unknown too — and a generated row is a specific piece of work handed to a person,
                // which may already be sitting in the file that could not be evaluated.
                return new Generator.GenerationResult(List.of(), List.of(),
                        List.of(new souther.compiler.partition.GenerationReason.RowsNotRead(
                                spec.name(), observed.incompleteness())));
            }
            List<RowOutcome> rows = observed.rows();
            List<String> parameters = spec.params().stream().map(Ast.Param::name).toList();
            souther.compiler.partition.Partitions.Partitioning partitioning =
                    Coverages.partitioningOf(spec, sig, symbols, body, plan, excluded);
            Generator.Subject subject = new Generator.Subject(parameters, sig.inputTypes(),
                    partitioning.axes(), symbols);
            Generator.CandidateCheck check = building == null ? Generator.CandidateCheck.ANY
                    : (at, candidate) -> building.refuse(sig.ins().get(at), candidate.value());

            List<Map<AxisId, Classification>> existing = rows.stream()
                    .map(row -> RowClasses.of(row, parameters, partitioning.axes())).toList();
            return Generator.fill(subject, existing, check);
        }
    }

    /**
     * A way to build values against this module's own classes, or nothing where there are none to
     * build against.
     *
     * <p>The classes an evaluation runs against, not a second generation of them. Whether a value
     * builds is the decoder's answer and the counting an evaluation carries does not change it —
     * nothing here runs a row, so no budget is installed and the counted entry points count against
     * nothing. Asking for the uncounted classes instead would generate every one of them again to get
     * the same answers.
     */
    static FixtureReader.Construction constructing(Db db, String module, Ast.Module written,
                                                   Symbols symbols) {
        Map<String, byte[]> classes =
                db.ask(new Output.EvaluationLinked(module, coverageAsked(db))).value();
        Map<String, List<BehaviorRequirement>> requirements =
                db.ask(new Bodies.Requirements(module)).value();
        if (classes == null || requirements == null) {
            return null;
        }
        Map<String, Ast.FnDef> values = db.ask(new Bodies.ModuleDefinitions(module)).value();
        // `requirements` is asked above as a readiness condition, not as an input: whether a
        // value builds at this module's boundary is the decoder's answer, and nothing here runs.
        return FixtureReader.constructing(written, symbols, classes,
                Output.evaluationLoader(db), values == null ? Map.of() : values);
    }

    /**
     * What one measure found and nothing filled.
     *
     * <p>Which of these fails a build is a property of the kind and not of whether it happens to carry
     * a diagnostic code. The two line up today, and a required finding that nobody gave a code to
     * would be a build that passes on a gap it printed, so the agreement is held by a test rather than
     * by reading one off the other.
     */
    public enum Kind {
        /** A case of the output no row expects. */
        OUTPUT_CASE_UNSPECIFIED(DiagnosticCode.E1913, true),
        /** A case of an input no row applies the behavior to. */
        INPUT_CASE_UNSPECIFIED(DiagnosticCode.E1915, true),
        /** A line some rule draws that no row sits on. */
        BOUNDARY_UNMET(DiagnosticCode.E1916, true),
        /** An arm of the body no row goes through. */
        ARM_UNREACHED(DiagnosticCode.E1918, true),
        /** A case some row expects and nothing was seen to produce. Not asked of an injected
         *  behavior, which has no body to produce anything. */
        OUTPUT_CASE_UNVERIFIED(null, false),
        /** A class of an axis no row is in. */
        AXIS_CLASS_UNCOVERED(null, false),
        /** A position the model draws no line through, which is a fact about the model. */
        PARTITION_NOT_DERIVABLE(null, false),
        /** A position left out because the axis limit was reached. */
        PARTITION_OMITTED(null, false);

        private final DiagnosticCode code;
        private final boolean adequacyGap;

        Kind(DiagnosticCode code, boolean adequacyGap) {
            this.code = code;
            this.adequacyGap = adequacyGap;
        }

        /** The code a build is told this under, where it is told at all. */
        public Optional<DiagnosticCode> code() {
            return Optional.ofNullable(code);
        }

        /** Whether a model carrying this one has not met what the rows are asked for. */
        public boolean isAdequacyGap() {
            return adequacyGap;
        }
    }

    /**
     * One thing a measure established, on the behavior it is about.
     *
     * <p>{@code args} are the message's arguments in the order its key takes them, which is also what
     * a report needs to write the line. Two spellings of the same finding would be two places to fix a
     * subject that changed name.
     *
     * <p>{@code status} is the measurement this came out of. A finding from a measurement that could
     * not be completed is worth printing — it says a row may be missing — and is not worth failing a
     * build over, because telling an author to write a row they may already have written is worse than
     * saying nothing.
     */
    public record Finding(Kind kind, String behavior, MeasurementStatus status, SourcePos at,
                          List<Object> args) {

        public Finding {
            args = List.copyOf(args);
        }

        /** Whether this is a gap a build is entitled to refuse: the kind is one, and the measurement
         *  behind it came to an answer. */
        public boolean isAdequacyGap() {
            return kind.isAdequacyGap() && status == MeasurementStatus.COMPLETE;
        }

        public Optional<DiagnosticCode> code() {
            return kind.code();
        }
    }

    /**
     * Everything the measures found, by behavior.
     *
     * <p>The one statement of what counts as a finding. A report prints these, a build is warned about
     * the ones that are gaps, and {@code souther examples --strict} refuses on the same ones — three
     * projections of this and no second reading of the evidence. Computed whether or not the build
     * asked to be warned, because a report wants them either way; what the level decides is which
     * measures were made at all.
     */
    public record Findings(String name) implements Key<Map<String, List<Finding>>> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, List<Finding>>> compute(Db db) {
            Level level = levelOf(db);
            Answer<Ast.Module> prepared = db.ask(new Shapes.Prepared(name));
            if (!prepared.present()) {
                return Answer.absent();
            }
            Map<String, SignatureEvidence> signatures =
                    level.reports() ? db.ask(new Witnesses(name)).value() : null;
            Map<String, PartitionEvidence> partitions =
                    level.measuresArms() ? db.ask(new Coverage(name)).value() : null;
            Map<String, BranchEvidence> branches =
                    level.measuresArms() ? db.ask(new BranchCoverage(name)).value() : null;

            Map<String, List<Finding>> out = new LinkedHashMap<>();
            for (Ast.BehaviorDef behavior : prepared.value().behaviors()) {
                List<Finding> found = new ArrayList<>();
                signatureFindings(behavior, prepared.value(),
                        signatures == null ? null : signatures.get(behavior.name()), found);
                partitionFindings(behavior,
                        partitions == null ? null : partitions.get(behavior.name()), found);
                armFindings(behavior,
                        branches == null ? null : branches.get(behavior.name()), found);
                out.put(behavior.name(), List.copyOf(found));
            }
            // Ordered, because a build reads the warnings these become and a set of warnings whose
            // order moves between runs is a diff nobody wrote.
            return Answer.of(Ordered.map(out));
        }

        /** What the rows say about the cases of the signature. Carried at the measurement's own status:
         *  a case nothing here claims is, where some row could not be read, a case nothing *seen*
         *  claims. */
        private static void signatureFindings(Ast.BehaviorDef behavior, Ast.Module module,
                                              SignatureEvidence signature, List<Finding> out) {
            if (signature == null || signature.status() == MeasurementStatus.UNAVAILABLE) {
                return;
            }
            MeasurementStatus status = signature.status();
            OutputCaseEvidence output = signature.output();
            for (TypeName missing : output.unspecified()) {
                out.add(new Finding(Kind.OUTPUT_CASE_UNSPECIFIED, behavior.name(), status,
                        behavior.pos(), List.of(missing.name(), behavior.name())));
            }
            // An injected behavior produces nothing, so every case of its output is unverified and
            // saying so of each says nothing. Left out here rather than at the printing, so that what
            // a report shows and what a build is told come from one list.
            if (!ExampleVerifier.isPending(module, behavior.name())) {
                for (TypeName missing : output.unverified()) {
                    if (!output.unspecified().contains(missing)) {
                        out.add(new Finding(Kind.OUTPUT_CASE_UNVERIFIED, behavior.name(), status,
                                behavior.pos(), List.of(missing.name(), behavior.name())));
                    }
                }
            }
            for (int i = 0; i < signature.inputs().size(); i++) {
                for (TypeName missing : signature.inputs().get(i).unspecified()) {
                    out.add(new Finding(Kind.INPUT_CASE_UNSPECIFIED, behavior.name(), status,
                            behavior.pos(), List.of(missing.name(), i + 1, behavior.name())));
                }
            }
        }

        /** What the rows reach of what the model distinguishes. A boundary is named only where the
         *  position was read on every row: a row writing the very number the rule names, whose
         *  observation was cut short elsewhere in the same input, is not a row that missed. */
        private static void partitionFindings(Ast.BehaviorDef behavior, PartitionEvidence partition,
                                              List<Finding> out) {
            if (partition == null) {
                return;
            }
            for (PartitionEvidence.AxisCoverage axis : partition.axes()) {
                // A class nothing sits in, where nothing was measured, is not a class no row is in.
                // Stopped here rather than where the line is printed: a finding is something a measure
                // established, and one from a measure that was never made is not established at all.
                if (axis.status() == MeasurementStatus.UNAVAILABLE) {
                    continue;
                }
                for (String missing : axis.uncovered()) {
                    out.add(new Finding(Kind.AXIS_CLASS_UNCOVERED, behavior.name(), axis.status(),
                            behavior.pos(), List.of(missing)));
                }
            }
            for (BoundaryAssessment boundary : partition.boundaries()) {
                // Both halves, asked of the two answers the assessment keeps apart. A line no row was
                // measured against is not a gap, and neither is one nothing has shown a row can be
                // written at — that edge is where the reading stopped rather than where the model
                // does, and a row at it may be one nobody can write.
                if (boundary.isUnmetGap()) {
                    out.add(new Finding(Kind.BOUNDARY_UNMET, behavior.name(),
                            MeasurementStatus.COMPLETE, behavior.pos(),
                            List.of(boundary.axis(), boundary.value(), boundary.origin())));
                }
            }
            for (String position : partition.notDerivable()) {
                out.add(new Finding(Kind.PARTITION_NOT_DERIVABLE, behavior.name(),
                        MeasurementStatus.COMPLETE, behavior.pos(), List.of(position)));
            }
            for (souther.compiler.partition.Partitions.OmittedAxis dropped : partition.omitted()) {
                out.add(new Finding(Kind.PARTITION_OMITTED, behavior.name(),
                        MeasurementStatus.COMPLETE, behavior.pos(),
                        List.of(dropped.axis().toString())));
            }
        }

        /** An arm no row goes through, at the arm and not at the declaration: what to do about it is
         *  written there. Named only where every row was read — an arm a row that never finished might
         *  have gone through is undecided, and calling it unreached sends the author after a row that
         *  exists. */
        private static void armFindings(Ast.BehaviorDef behavior, BranchEvidence branch,
                                        List<Finding> out) {
            if (branch == null || branch.status() != MeasurementStatus.COMPLETE) {
                return;
            }
            for (souther.compiler.coverage.CoverageSites.Site arm : branch.unreached()) {
                out.add(new Finding(Kind.ARM_UNREACHED, behavior.name(), branch.status(),
                        arm.at().pos(), List.of(arm.label(), arm.behavior())));
            }
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
            Answer<Map<String, List<Finding>>> found = db.ask(new Findings(name));
            if (!found.present()) {
                return Answer.absent();
            }
            List<Report> reports = new ArrayList<>();
            for (List<Finding> ofBehavior : found.value().values()) {
                for (Finding finding : ofBehavior) {
                    if (finding.isAdequacyGap()) {
                        reports.add(warning(finding));
                    }
                }
            }
            return Answer.of(true, reports);
        }

        /**
         * One finding as the warning a build reads.
         *
         * <p>The message keys are written out per kind rather than derived from the code's name, so
         * that a scan for the keys this names finds them — a key built by concatenation is one nothing
         * can see is used. Which findings get here is {@link Finding#isAdequacyGap()}'s answer and not
         * this method's.
         */
        private static Report warning(Finding finding) {
            DiagnosticCode code = finding.code().orElseThrow();
            souther.compiler.diag.Diagnostic.Builder built =
                    souther.compiler.diag.Diagnostic.of(code, messageKey(finding.kind())).warning()
                            .at(finding.at())
                            .args(finding.args().toArray());
            switch (finding.kind()) {
                case OUTPUT_CASE_UNSPECIFIED ->
                        built.hint("check.example.witness.out.hint", finding.args().get(0));
                case BOUNDARY_UNMET -> built.hint("check.example.boundary.hint");
                case ARM_UNREACHED -> built.hint("check.example.unreachedarm.hint");
                default -> { }   // the message says all there is to say
            }
            return Report.of(built.build());
        }

        private static String messageKey(Kind kind) {
            return switch (kind) {
                case OUTPUT_CASE_UNSPECIFIED -> "check.example.witness.out";
                case INPUT_CASE_UNSPECIFIED -> "check.example.witness.in";
                case BOUNDARY_UNMET -> "check.example.boundary";
                case ARM_UNREACHED -> "check.example.unreachedarm";
                default -> throw new IllegalArgumentException("no message for " + kind);
            };
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

    /**
     * @param parameters the behavior's parameter names, which is how an exclusion read off the body
     *                   at an input position is matched to the position this counts
     */
    static SignatureEvidence evidenceOf(Sig sig, Symbols symbols, Observed seen,
                                        List<String> parameters, Exclusions excluded,
                                        souther.compiler.core.Core body,
                                        souther.compiler.coverage.CoverageSites.Plan plan,
                                        Effective reachable) {
        List<RowOutcome> rows = seen.rows();
        // The cases the output type has, less the ones only an arm nothing reaches produces. A case
        // no reachable producer answers with is not a gap in the rows.
        Set<TypeName> declaredOut = souther.compiler.partition.ProducedCases.of(
                body, plan, reachable.reachable(), coverableCases(sig.outputType(), symbols));
        Set<TypeName> specified = new LinkedHashSet<>();
        Set<TypeName> observed = new LinkedHashSet<>();
        Set<TypeName> verified = new LinkedHashSet<>();
        int unreadableOut = 0;

        List<Type> ins = sig.inputTypes();
        List<Set<TypeName>> declaredIn = new ArrayList<>(ins.size());
        List<Set<TypeName>> inSpecified = new ArrayList<>(ins.size());
        List<Set<TypeName>> inExecuted = new ArrayList<>(ins.size());
        List<Set<TypeName>> inVerified = new ArrayList<>(ins.size());
        List<Set<TypeName>> inExcluded = new ArrayList<>(ins.size());
        int[] unreadableIn = new int[ins.size()];
        for (int i = 0; i < ins.size(); i++) {
            Set<TypeName> declared = coverableCases(ins.get(i), symbols);
            declaredIn.add(declared);
            inSpecified.add(new LinkedHashSet<>());
            inExecuted.add(new LinkedHashSet<>());
            inVerified.add(new LinkedHashSet<>());
            // Matched within the position it was read at: a class is named the same way at every
            // position of the same type, and one behaviour's `Off` arm says nothing about another
            // input that is also a `Flag`.
            List<TypeName> here = i < parameters.size()
                    ? excluded.atParameter(parameters.get(i)) : List.of();
            inExcluded.add(here.stream().filter(declared::contains)
                    .collect(java.util.stream.Collectors.toCollection(LinkedHashSet::new)));
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
                            inVerified.get(i), inExcluded.get(i), unreadableIn[i]);
            inputs.add(evidence);
            partial |= evidence.status() == MeasurementStatus.PARTIAL;
        }
        // Nothing was measured where nothing was written: a behavior with no rows has no gaps to
        // report, only an absence of evidence, and saying so is not the same as saying it is covered.
        // A source that could not be evaluated is a set of rows nothing has seen, and a case they may
        // have covered reads exactly like a case nothing covers. A row that did not finish is already
        // counted, above: its state is dropped rather than read, so it has no arm and no input case
        // and shows up as one nothing could classify.
        partial |= seen.someRowsUnseen();
        if (rows.isEmpty() && seen.complete()) {
            return SignatureEvidence.unavailable(output, inputs, SignatureEvidence.Reason.NO_ROWS);
        }
        return new SignatureEvidence(output, inputs,
                partial ? MeasurementStatus.PARTIAL : MeasurementStatus.COMPLETE, null);
    }

    private Adequacy() {}
}
