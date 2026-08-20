package souther.compiler.query;

import souther.compiler.inputs.TermPath;
import souther.compiler.source.SourceId;


import souther.compiler.diag.DiagnosticCode;
import souther.compiler.diag.msg.DeadBranchMessage;
import souther.compiler.diag.msg.ExampleMessage;
import souther.compiler.diag.Citation;
import souther.compiler.diag.SourcePos;
import souther.compiler.examples.FixtureReader;
import souther.compiler.ast.Hir;
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
import souther.compiler.observe.Counting;
import souther.compiler.observe.RowOutcome;
import souther.compiler.observe.Stage;
import souther.compiler.partition.Axis;
import souther.compiler.partition.AxisId;
import souther.compiler.inputs.InputDomain;
import souther.compiler.partition.GenerationOutcome;
import souther.compiler.partition.Generator;
import souther.compiler.partition.RowClasses;
import souther.compiler.types.Type;
import souther.compiler.types.TypeSymbol;

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
    /** Nothing read, so nothing proven and nothing shown wrong. What a measure gets where the
     *  reading is not available, which leaves every arm owed whatever it was owed. */
    static final souther.compiler.check.PathReachability.Answers.AsRun NOTHING_PROVEN =
            new souther.compiler.check.PathReachability.Answers.AsRun(souther.compiler.check.PathReachability.Answers.NONE, Set.of());

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
        public enum Reason implements souther.compiler.observe.MeasureReason {
            /** No row names this behavior, so nothing was established about it either way. */
            NO_ROWS(MeasurementStatus.NOT_MEASURED),
            /** Neither the output nor any input is a sum, so there is no case anywhere for a row to
             *  cover and no row could make one. Held here rather than read back from the two empty
             *  case sets below it: a reader that counted them would be answering a different
             *  question — how many cases there are — and getting this one right by coincidence. */
            NOT_A_SUM(MeasurementStatus.NOT_APPLICABLE);

            private final MeasurementStatus status;

            Reason(MeasurementStatus status) {
                this.status = status;
            }

            @Override
            public MeasurementStatus status() {
                return status;
            }
        }

        public static SignatureEvidence unavailable(OutputCaseEvidence output,
                                                    List<InputCaseEvidence> inputs, Reason reason) {
            return new SignatureEvidence(output, inputs, reason.status(), reason);
        }

        public SignatureEvidence {
            inputs = List.copyOf(inputs);
            // And each of them where it says it is. Two things say which input a piece of evidence
            // is about — where it sits in this list, which is what the document publishes as the
            // order of `signature.inputs`, and what the evidence answers, which is what a finding
            // names a position by. They are read by different surfaces, so a list assembled out of
            // step would publish an array whose first entry called itself the second, and each
            // surface would go on being right about the one it reads.
            //
            // Held here because here is where both exist. The evidence carries the position so that
            // one of them means something away from this list, and the price of that is that the
            // two can be said to differ; this is where they are said to agree.
            for (int i = 0; i < inputs.size(); i++) {
                if (inputs.get(i).at() != i) {
                    throw new IllegalArgumentException("the evidence at input " + i
                            + " says it is input " + inputs.get(i).at());
                }
            }
            Unavailable.check(status, reason);
        }
    }

    /**
     * What can arrive at each position of each behavior's input, in this module.
     *
     * <p>Asked once, here, and read by every measure that needs a denominator. What a signature's
     * cases are, what a position divides into, what arms a row is owed and what a body's
     * {@code unreachable} claims are held against are projections of one reading, and deriving that
     * reading per measure is what let a case the rules refuse stay in one denominator while another
     * had already taken it out.
     */
    public record Inputs(String name) implements Key<Map<String, InputDomain>> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, InputDomain>> compute(Db db) {
            Answer<souther.compiler.check.Prepared> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = Names.derivedSymbols(db, name);
            Answer<Map<String, Sig>> sigs = db.ask(new Bodies.Signatures(name));
            Answer<Hir.Module> settled = db.ask(new Bodies.Settled(name));
            if (!prepared.present() || !scope.present() || !sigs.present() || !settled.present()) {
                return Answer.absent();
            }
            // A module holding a type nothing could be worked out for is one this says nothing
            // about. The hole was reported where the name is, and what a case can arrive at cannot
            // be read through one — asked anyway, the reading meets a shape no position can have
            // and says so about this compiler, which is true and is not what the author of a
            // mistyped model needs.
            if (souther.compiler.check.TypeOps.holdsAnErroneousType(settled.value())) {
                return Answer.absent();
            }
            Map<String, InputDomain> out = new LinkedHashMap<>();
            for (Hir.BehaviorDef behavior : prepared.value().behaviors()) {
                if (!(behavior instanceof Hir.SpecBehavior spec)) {
                    continue;   // a composition's inputs are its first stage's, read there
                }
                Sig sig = sigs.value().get(spec.name());
                if (sig != null) {
                    // The implementation the body was checked against, which is where a read of a
                    // parameter gets the binding it carries: the check binds `fn`'s own binders and
                    // the lowering leaves them alone. A behavior nothing implements has positions
                    // all the same.
                    Answer<Hir.FnDef> fn = db.ask(new Bodies.SettledFn(name, spec.name()));
                    out.put(spec.name(), InputDomain.of(spec, fn.present() ? fn.value() : null, sig,
                            scope.value()));
                }
            }
            return Answer.of(Ordered.map(out));
        }
    }

    /**
     * One behavior's reading, or an empty one where the module's could not be made.
     *
     * <p>An absent reading is not a reading that found nothing: the difference is what the caller
     * goes on to say, and what it may say about a behavior whose signature is not in hand is
     * nothing. Written once so that each reader does not decide again what to do without one.
     */
    private static souther.compiler.check.PathReachability.Answers arrivalsOf(
            Map<String, souther.compiler.check.PathReachability.Answers> read,
            Hir.SpecBehavior spec) {
        return read == null ? souther.compiler.check.PathReachability.Answers.NONE
                : read.getOrDefault(spec.name(),
                        souther.compiler.check.PathReachability.Answers.NONE);
    }

    private static InputDomain domainOf(Map<String, InputDomain> read, Hir.SpecBehavior spec) {
        return read == null ? InputDomain.NONE
                : read.getOrDefault(spec.name(), InputDomain.NONE);
    }

    /** What one behavior states about its answer, or nothing where it states none. A behavior
     *  declaring nothing is not in the map at all, which is what says it states nothing. */
    private static souther.compiler.check.StatedContract statedOf(
            Map<String, souther.compiler.check.StatedContract> declared, Hir.SpecBehavior spec) {
        return declared == null ? null : declared.get(spec.name());
    }


    /**
     * What the model's own rules say arrives at each place of each behavior of one module.
     *
     * <p>Asked once and here, for the reason every other reading of this is: what a position is
     * divided into, which lines are owed a row, which arms are owed one and what a body declares
     * about a case are projections of one universe of possible executions, and a derivation per
     * measure is a chance per measure to disagree.
     *
     * <p>What this adds to {@link Reachable} is the conditions on the way. That one holds a
     * comparison against what the declarations leave a position, which is the same answer wherever
     * in a body the comparison stands — so a guard whose departure the guards above it have already
     * ruled out came back as an arm still owed a row.
     */
    public record PathReached(String name)
            implements Key<Map<String, souther.compiler.check.PathReachability.Answers>> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, souther.compiler.check.PathReachability.Answers>> compute(Db db) {
            Answer<souther.compiler.check.Prepared> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = Names.derivedSymbols(db, name);
            if (!prepared.present() || !scope.present()) {
                return Answer.absent();
            }
            souther.compiler.query.Bodies.Elaborated checked =
                    db.ask(new Bodies.Checked(name)).value();
            Map<String, souther.compiler.core.Core> bodies =
                    checked == null ? Map.of() : checked.behaviorBodies();
            if (bodies.isEmpty()) {
                // Nothing checked, so there are no places to be about. Asked further, the reading
                // of the input is derived over types that did not check — which is a position the
                // partition refuses outright, and rightly: what would be answered there is about
                // this compile having stopped and not about the model.
                return Answer.of(Ordered.map(Map.of()));
            }
            souther.compiler.coverage.CoverageSites.Plan plan =
                    souther.compiler.coverage.CoverageSites.of(bodies);
            Map<String, InputDomain> readInputs = db.ask(new Inputs(name)).value();
            Map<String, souther.compiler.check.PathReachability.Answers> out = new LinkedHashMap<>();
            for (Hir.BehaviorDef behavior : prepared.value().behaviors()) {
                if (!(behavior instanceof Hir.SpecBehavior spec)) {
                    continue;   // a composition has no body of its own, so no places of its own
                }
                souther.compiler.core.Core body = bodies.get(spec.name());
                Hir.FnDef fn = db.ask(new Bodies.SettledFn(name, spec.name())).value();
                if (body == null || fn == null) {
                    continue;
                }
                out.put(spec.name(), souther.compiler.check.PathReachability.of(
                        body, spec, fn, plan, domainOf(readInputs, spec), scope.value()));
            }
            return Answer.of(Ordered.map(out));
        }
    }

    /**
     * The branches of one module that the model's own rules make dead.
     *
     * <p>The other half of the proof {@link PathReached} makes. One reading, two readers, and they
     * are not the same reader: taking an obligation away leaves an author with less to do, and
     * saying a branch is dead tells them something is wrong. What keeps them apart is that both act
     * on {@link Reachability.Unreachable} and neither acts on anything else — an unsettled place
     * keeps its rows and is said nothing about.
     *
     * <p>Not gated on what the build asked to measure. A dead branch is a defect in the model and
     * not a gap in its rows, so it is said whether or not anybody asked for a coverage report.
     */
    public record DeadBranches(String name) implements Key<Boolean> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Boolean> compute(Db db) {
            // What arrives once the rows have run, which is what every other consumer reads. A row
            // that went through an arm this reading had proven nothing reaches settles it: what
            // happened happened, the proof was wrong rather than the row, and warning about it
            // would be a false report about a model the rows have already shown is fine.
            Answer<Map<String, souther.compiler.check.PathReachability.Answers.AsRun>> arrives =
                    db.ask(new Arrived(name));
            if (!arrives.present()) {
                return Answer.absent();
            }
            // In the order an author reads them. The walk numbers an inner fork while it is inside
            // the arm that holds it, so the order it finds things in is a fact about the traversal;
            // where a warning sits in the output should be a fact about the source.
            List<Dead> found = new ArrayList<>();
            arrives.value().forEach((behavior, asRun) -> asRun.answers().found()
                    .forEach((where, said) -> {
                        // Only the forks this module's own source wrote. A call into another
                        // module splices that module's forks in here, and an argument this call
                        // site hands them can leave one of their arms unreachable — which is true,
                        // and is a fact about the call rather than a defect in either module. The
                        // author cannot take that branch out; it is not theirs.
                        // An arm a run could have been recorded in. An arm that answers nothing —
                        // the `unreachable` an author writes at a case the rules refuse — is not
                        // one: it is the author saying what this reading proves, and telling them
                        // to take it out is telling them off for being right. The denominator
                        // counts the probed arms, and this reports the probed arms.
                        if (where instanceof souther.compiler.coverage.ControlPointId.ArmOccurrence
                                arm && arm.isMeasured() && arm.writtenBy(name)
                                && said instanceof souther.compiler.reach.Reachability.Unreachable
                                        unreachable) {
                            found.add(new Dead(arm, unreachable.proof()));
                        }
                    }));
            // In the order an author reads them. The walk numbers an inner fork while it is inside
            // the arm that holds it, so what order it finds them in is a fact about the traversal;
            // where a warning sits in the output should be a fact about the source.
            found.sort(java.util.Comparator.comparingInt((Dead each) -> at(each.arm()).line())
                    .thenComparingInt(each -> at(each.arm()).column()));
            List<Report> reports = new ArrayList<>();
            for (Dead each : found) {
                reports.add(warning(each.arm(), each.proof()));
            }
            return Answer.of(true, reports);
        }

        /**
         * One dead branch as the warning a build reads.
         *
         * <p><b>The one place a proof is taken apart.</b> The switch is exhaustive with no default,
         * so a proof added to the reading stops here and is given words, rather than falling into a
         * sentence written for something else. Everything that decides anything reads the three
         * answers and never this.
         */
        private static Report warning(
                souther.compiler.coverage.ControlPointId.ArmOccurrence arm,
                souther.compiler.reach.Proof proof) {
            return Report.of(new DeadBranchProofWords(
                    Warnings.pointedAt(arm.at())
                            .say(new DeadBranchMessage.NothingReachesThisBranch()))
                    .of(proof)
                    .hint(new DeadBranchMessage.TakeItOutOrLetSomethingReachIt())
                    .build());
        }

        /**
         * The one place a proof is turned into words.
         *
         * <p>Named rather than written where it is used, so that what may ask a proof what it says
         * is one class and can be held to being one: the check that fixes this reads the compiled
         * calls, and a class with a name is what it can name.
         *
         * <p>It says a word for every arm or does not compile. A proof's arms are not types this
         * package can name, so there is no switch to fall through and no default to write.
         */
        private record DeadBranchProofWords(souther.compiler.diag.Diagnostic.Builder said)
                implements souther.compiler.reach.Proof.Words<
                        souther.compiler.diag.Diagnostic.Builder> {

            /** What {@code proof} says, in these words. */
            souther.compiler.diag.Diagnostic.Builder of(souther.compiler.reach.Proof proof) {
                return proof.said(this);
            }

            @Override
            public souther.compiler.diag.Diagnostic.Builder conditionsThatCannotAllHold(
                    List<souther.compiler.reach.PathDecision> decisions) {
                return said.hint(new DeadBranchMessage.TheConditionsOnTheWayHereCannotAllHold(
                        decisions.stream()
                                .map(each -> "line " + each.at().line()
                                        + (each.held() ? " holding" : " failing"))
                                .collect(java.util.stream.Collectors.joining(", "))));
            }

            @Override
            public souther.compiler.diag.Diagnostic.Builder outsideInputDomain(
                    souther.compiler.inputs.TermPath position,
                    souther.compiler.numeric.NumericDomain.Bounds admits,
                    souther.compiler.reach.PathDecision departure) {
                return said.hint(new DeadBranchMessage.ThePositionStopsShortOfIt(
                        position.toString(), shown(admits)));
            }

            /**
             * What a position's values come to, as an author reads them.
             *
             * <p>In the shape a generated row's name is written in, so that the sentence about a
             * branch and the row a report offers beside it say a range the same way. An end nothing
             * bounds is left out rather than written as an infinity nobody typed.
             */
            private static String shown(souther.compiler.numeric.NumericDomain.Bounds admits) {
                String low = admits.min() == null ? null
                        : admits.min().at() + (admits.min().inclusive() ? " <= " : " < ");
                String high = admits.max() == null ? null
                        : (admits.max().inclusive() ? " <= " : " < ") + admits.max().at();
                return low == null && high == null ? "any number"
                        : (low == null ? "x" : low + "x") + (high == null ? "" : high);
            }

            @Override
            public souther.compiler.diag.Diagnostic.Builder everyCaseRefused(
                    String position, List<souther.compiler.types.TypeSymbol> cases) {
                return said.hint(new DeadBranchMessage.EveryCaseItIsWrittenForIsRefused(
                        position,
                        cases.stream().map(souther.compiler.types.TypeSymbol::name)
                                .collect(java.util.stream.Collectors.joining(", "))));
            }
        }

        /** One dead branch and how it was shown, before either is turned into words. */
        private record Dead(souther.compiler.coverage.ControlPointId.ArmOccurrence arm,
                            souther.compiler.reach.Proof proof) {}

        /** Where an arm is written, read the way {@link Warnings#pointedAt} reads it. */
        private static souther.compiler.diag.SourcePos at(
                souther.compiler.coverage.ControlPointId.ArmOccurrence arm) {
            return switch (arm.at()) {
                case Citation.Written written -> written.at();
                case Citation.Unplaced unplaced -> unplaced.at();
                case Citation.Reached reached -> reached.at();
                case Citation.UnplacedElsewhere out -> out.at();
                // Nowhere to point, so nothing to order it by. First, and the same first every run.
                case Citation.OutOfSight _ -> new souther.compiler.diag.SourcePos(0, 0);
            };
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
    public record Arrived(String name)
            implements Key<Map<String, souther.compiler.check.PathReachability.Answers.AsRun>> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, souther.compiler.check.PathReachability.Answers.AsRun>>
                compute(Db db) {
            Answer<Map<String, souther.compiler.check.PathReachability.Answers>> proven =
                    db.ask(new PathReached(name));
            if (!proven.present()) {
                return Answer.absent();
            }
            Set<Integer> lit = new LinkedHashSet<>();
            for (Observed observed : rowsOf(db, name).values()) {
                for (RowOutcome row : observed.rows()) {
                    lit.addAll(litBy(row));
                }
            }
            Map<String, souther.compiler.check.PathReachability.Answers.AsRun> out =
                    new LinkedHashMap<>();
            proven.value().forEach((behavior, answers) -> out.put(behavior, answers.asRunWith(lit)));
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
            Answer<souther.compiler.check.Prepared> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = Names.derivedSymbols(db, name);
            Answer<Map<String, Sig>> sigs = db.ask(new Bodies.Signatures(name));
            if (!prepared.present() || !scope.present() || !sigs.present()) {
                return Answer.absent();
            }
            Map<String, Observed> byTarget = rowsOf(db, name);
            Map<String, InputDomain> readInputs = db.ask(new Inputs(name)).value();
            // What each body can answer with, so that a case only an unreachable arm produces is not
            // counted. Read from the same reachability the arms are counted by.
            souther.compiler.query.Bodies.Elaborated checkedBodies =
                    db.ask(new Bodies.Checked(name)).value();
            Map<String, souther.compiler.core.Core> producing =
                    checkedBodies == null ? Map.of() : checkedBodies.behaviorBodies();
            souther.compiler.coverage.CoverageSites.Plan producingPlan =
                    souther.compiler.coverage.CoverageSites.of(producing);
            Map<String, souther.compiler.check.PathReachability.Answers.AsRun> reachableArms = db.ask(new Arrived(name)).value();
            Map<String, SignatureEvidence> out = new LinkedHashMap<>();
            for (Hir.BehaviorDef behavior : prepared.value().behaviors()) {
                Sig sig = sigs.value().get(behavior.name());
                if (sig == null) {
                    continue;   // a behavior whose signature did not work out has nothing to measure
                }
                out.put(behavior.name(), evidenceOf(sig, scope.value(),
                        byTarget.getOrDefault(behavior.name(), Observed.NONE),
                        behavior instanceof Hir.SpecBehavior spec ? spec.params().stream()
                                .map(Hir.Param::name).toList() : List.of(),
                        readInputs == null ? InputDomain.NONE
                                : readInputs.getOrDefault(behavior.name(), InputDomain.NONE),
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
            Answer<souther.compiler.check.Prepared> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = Names.derivedSymbols(db, name);
            Answer<Map<String, Sig>> sigs = db.ask(new Bodies.Signatures(name));
            if (!prepared.present() || !scope.present() || !sigs.present()) {
                return Answer.absent();
            }
            souther.compiler.query.Bodies.Elaborated checked =
                    db.ask(new Bodies.Checked(name)).value();
            Map<String, souther.compiler.core.Core> bodies =
                    checked == null ? Map.of() : checked.behaviorBodies();
            souther.compiler.coverage.CoverageSites.Plan plan =
                    souther.compiler.coverage.CoverageSites.of(bodies);
            Map<String, Observed> byTarget = rowsOf(db, name);
            Map<String, InputDomain> readInputs = db.ask(new Inputs(name)).value();
            // What the guards above each place leave, asked once for the module and read by
            // every measure below — the same reason the reading of the input is.
            Map<String, souther.compiler.check.PathReachability.Answers> arrives =
                    db.ask(new PathReached(name)).value();
            // What every line this module's rules drew came to, asked once and read here. Measuring a
            // line takes building values, which is not this measure's work and not work to do twice.
            Map<String, List<BorderAssessment>> boundaries = db.ask(new Boundaries(name)).value();
            // What each behavior states about its answer, read into the representation the analysis
            // holds it in. A comparison written there draws a line as a `guard`'s does.
            Map<String, souther.compiler.check.StatedContract> declared =
                    db.ask(new Bodies.StatedContracts(name)).value();

            Map<String, PartitionEvidence> out = new LinkedHashMap<>();
            for (Hir.BehaviorDef behavior : prepared.value().behaviors()) {
                if (!(behavior instanceof Hir.SpecBehavior spec)) {
                    continue;   // a composition's inputs are its first stage's, measured there
                }
                Sig sig = sigs.value().get(spec.name());
                if (sig == null) {
                    continue;
                }
                Observed seen = byTarget.getOrDefault(spec.name(), Observed.NONE);
                // Counted with nothing a body claims in scope. What was claimed travels beside the
                // numbers rather than into them ({@link Claimed}), and the two meet where a report
                // is written.
                out.put(spec.name(), Coverages.of(spec, domainOf(readInputs, spec), sig,
                        scope.value(), bodies.get(spec.name()), plan, seen,
                        boundaries == null ? List.of()
                                : boundaries.getOrDefault(spec.name(), List.of()),
                        arrivalsOf(arrives, spec), statedOf(declared, spec)));
            }
            return Answer.of(Ordered.map(out));
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
    public record Boundaries(String name) implements Key<Map<String, List<BorderAssessment>>> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, List<BorderAssessment>>> compute(Db db) {
            Answer<souther.compiler.check.Prepared> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = Names.derivedSymbols(db, name);
            Answer<Map<String, Sig>> sigs = db.ask(new Bodies.Signatures(name));
            if (!prepared.present() || !scope.present() || !sigs.present()) {
                return Answer.absent();
            }
            souther.compiler.query.Bodies.Elaborated checked =
                    db.ask(new Bodies.Checked(name)).value();
            Map<String, souther.compiler.core.Core> bodies =
                    checked == null ? Map.of() : checked.behaviorBodies();
            souther.compiler.coverage.CoverageSites.Plan plan =
                    souther.compiler.coverage.CoverageSites.of(bodies);
            Map<String, Observed> byTarget = rowsOf(db, name);
            Map<String, InputDomain> readInputs = db.ask(new Inputs(name)).value();
            // What the guards above each place leave, asked once for the module and read by
            // every measure below — the same reason the reading of the input is.
            Map<String, souther.compiler.check.PathReachability.Answers> arrives =
                    db.ask(new PathReached(name)).value();
            Symbols symbols = scope.value();
            // Whether a guard's boundary can be decided at all: meeting it takes the comparison having
            // been evaluated, which only the instrumented classes say.
            boolean armsAsked = levelOf(db).measuresArms();
            FixtureReader.Construction building = constructing(db, name,
                    prepared.value().forExamples(), symbols);
            // And what each behavior states about its answer, which draws lines of its own.
            Map<String, souther.compiler.check.StatedContract> declared =
                    db.ask(new Bodies.StatedContracts(name)).value();

            Map<String, List<BorderAssessment>> out = new LinkedHashMap<>();
            for (Hir.BehaviorDef behavior : prepared.value().behaviors()) {
                if (!(behavior instanceof Hir.SpecBehavior spec)) {
                    continue;   // a composition's inputs are its first stage's, measured there
                }
                Sig sig = sigs.value().get(spec.name());
                if (sig == null) {
                    continue;
                }
                out.put(spec.name(), assess(spec, sig, symbols, bodies.get(spec.name()), plan,
                        byTarget.getOrDefault(spec.name(), Observed.NONE), armsAsked, building,
                        domainOf(readInputs, spec), arrivalsOf(arrives, spec),
                        statedOf(declared, spec)));
            }
            return Answer.of(Ordered.map(out));
        }

        /** Every line of one behavior, with what the rows and the decoder say about each. */
        private static List<BorderAssessment> assess(
                Hir.SpecBehavior spec, Sig sig, Symbols symbols, souther.compiler.core.Core body,
                souther.compiler.coverage.CoverageSites.Plan plan, Observed observed,
                boolean armsAsked, FixtureReader.Construction building, InputDomain domain,
                souther.compiler.check.PathReachability.Answers arrives,
                souther.compiler.check.StatedContract stated) {
            List<String> parameters = spec.params().stream().map(Hir.Param::name).toList();
            souther.compiler.partition.BehaviorInputs inputs =
                    new souther.compiler.partition.BehaviorInputs(parameters, sig.inputTypes(),
                            symbols);
            souther.compiler.partition.Partitions.Partitioning partitioning =
                    Coverages.partitioningOf(spec, domain, sig, symbols, body, plan, arrives,
                            stated);
            Coverages.Probe probe = probing(partitioning, sig, symbols, parameters, building);
            // Two sources and not one. A line drawn at a count of a position comes off that position's
            // axis; a line drawn between two positions comes off the comparison and has no axis to come
            // off — the body of a behavior whose inputs are plain numbers nothing bounds draws lines
            // while having no axis at all.
            List<BorderAssessment> out = new ArrayList<>();
            for (Axis axis : partitioning.axes()) {
                if (!axis.measurable()) {
                    continue;
                }
                out.addAll(Coverages.assess(axis, inputs, observed, armsAsked,
                        partitioning.edgeIsKnownWritable(axis.term()), probe,
                        partitioning.domains().get(axis.term())));
            }
            out.addAll(Coverages.assessBetween(partitioning, inputs, observed, armsAsked, probe));
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
            Generator.Subject subject = new Generator.Subject(
                    new souther.compiler.partition.BehaviorInputs(parameters, sig.inputTypes(),
                            symbols), partitioning.axes());
            Generator.CandidateCheck check =
                    (at, candidate) -> building.refuse(sig.ins().get(at), candidate.value());
            return new Coverages.Probe() {

                @Override
                public Generator.BoundaryAttempt attempt(String label,
                        souther.compiler.check.Carrier carrier,
                        java.util.Map<souther.compiler.inputs.NumericTerm,
                                souther.compiler.numeric.Place> fixing) {
                    return built(() ->
                            Generator.probeFixing(subject, label, carrier, fixing, check));
                }

                private Generator.BoundaryAttempt built(
                        java.util.function.Supplier<Generator.BoundaryAttempt> attempt) {
                    try {
                        return attempt.get();
                    } catch (LinkageError _) {
                        // The generated classes would not link, so nothing can be built to find out
                        // what a model admits. Nothing was tried, which is not the same as everything
                        // tried being refused, and neither of them says the edge cannot be written.
                        return null;
                    }
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
     *                Which arms those are is {@link ArmReachability}'s answer, asked once for the
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
        public enum Reason implements souther.compiler.observe.MeasureReason {
            /** A {@code >->} composition or a behavior with no {@code let}. It has no arms of its own,
             *  so the measure does not apply rather than failing. */
            NO_BODY(MeasurementStatus.NOT_APPLICABLE),
            /** The build did not ask for the arms, which cost a second run of every row. */
            NOT_ASKED(MeasurementStatus.NOT_MEASURED),
            /** The rows ran without instrumentation, so what they went through went with it. */
            UNREADABLE(MeasurementStatus.NOT_MEASURED),
            /** No row names this behavior. The measurement is opted into by writing one, and reaching
             *  the behavior through somebody else's row is not opting in. */
            NO_ROWS(MeasurementStatus.NOT_MEASURED);

            private final MeasurementStatus status;

            Reason(MeasurementStatus status) {
                this.status = status;
            }

            @Override
            public MeasurementStatus status() {
                return status;
            }
        }

        public static BranchEvidence unavailable(Reason reason) {
            return new BranchEvidence(List.of(), Set.of(), Set.of(), reason.status(), reason);
        }

        /**
         * The arms of one behavior, with the ones nothing reaches taken out of what it is owed.
         *
         * <p>Taken out here and not where the probes are numbered. The plan says where instrumentation
         * is; this says which of it is owed a row, and the two are different questions — a site with no
         * probe could never disprove the reachability it was excluded by.
         */
        public static BranchEvidence measured(List<souther.compiler.coverage.CoverageSites.Site> all,
                                              Set<Integer> covered, souther.compiler.check.PathReachability.Answers.AsRun reachable,
                                              MeasurementStatus status) {
            List<souther.compiler.coverage.CoverageSites.Site> owed = all.stream()
                    .filter(site -> !reachable.answers().nothingArrivesAt(site.index())).toList();
            Set<Integer> counted = new LinkedHashSet<>(covered);
            counted.retainAll(owed.stream()
                    .map(souther.compiler.coverage.CoverageSites.Site::index).toList());
            // A proof a row has already disproved is not something to report a complete measurement
            // over. What is wrong is this analysis, not the model's rows, and a number given as though
            // nothing had happened is the one thing that must not come out of it.
            return new BranchEvidence(owed, counted, reachable.provedWrong(),
                    reachable.provedWrong().isEmpty() ? status : MeasurementStatus.PARTIAL, null);
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
         * <p>Read off the status, which now has a word for it. This used to ask after
         * {@link Reason#NO_BODY} because {@code MeasurementStatus} had none, and every caller that
         * needed the distinction had to know this measure's reasons to get it.
         */
        public boolean applicable() {
            return status != MeasurementStatus.NOT_APPLICABLE;
        }

        /**
         * The occurrences of each arm this behavior is owed a row for, in the order the body holds
         * them.
         *
         * <p>Where the quotient is taken, and the only place. Everything below this — the probes, the
         * proofs about what can reach what — is about one occurrence at a time, because a copy of an
         * arm spliced under one call site is reachable on terms the copy under the next one does not
         * share. What a row is owed for is the arm the author wrote, so the counts and the findings
         * above this line are per key and not per copy.
         */
        private java.util.SequencedMap<souther.compiler.coverage.CoverageSites.Obligation,
                List<souther.compiler.coverage.CoverageSites.Site>> byObligation() {
            java.util.SequencedMap<souther.compiler.coverage.CoverageSites.Obligation,
                    List<souther.compiler.coverage.CoverageSites.Site>> out = new LinkedHashMap<>();
            for (souther.compiler.coverage.CoverageSites.Site site : all) {
                out.computeIfAbsent(site.obligation(), _ -> new ArrayList<>()).add(site);
            }
            return out;
        }

        /**
         * How many arms this behavior is owed a row for.
         *
         * <p>An arm is owed where something can reach any one of its occurrences: a helper called down
         * a path a proof rules out is still owed rows through the paths it is called down elsewhere,
         * and an arm nothing at all can reach was already taken out of {@link #all}.
         */
        public int obligations() {
            return byObligation().size();
        }

        /** How many of them some row goes through — through any one occurrence, since going through
         * an arm is going through it whichever call site the row arrived by. */
        public int coveredObligations() {
            int hit = 0;
            for (List<souther.compiler.coverage.CoverageSites.Site> occurrences
                    : byObligation().values()) {
                if (occurrences.stream().anyMatch(site -> covered.contains(site.index()))) {
                    hit++;
                }
            }
            return hit;
        }

        /**
         * The arms no row goes through, one entry per arm.
         *
         * <p>Named at the first occurrence the body holds. Where the copies keep the positions they
         * were written at they all say the same thing; where a copy could not — the body came from a
         * module this compile has no source for, so each copy was given the call site that spliced it
         * — the occurrences are at different places and one of them has to be the one shown, since
         * the arm is one arm and the report says so once.
         *
         * <p>Which one is a choice about where to send a reader and not about where the arm is. What
         * each occurrence carries says the arm is written out of sight and names the declaration, so
         * the report says that however this chooses; the choice only decides which call the reader is
         * shown. A module of this compile that declares the helper is not this case at all — its body
         * is in a file the reader holds, and every copy keeps its own positions.
         */
        public List<souther.compiler.coverage.CoverageSites.Site> unreached() {
            List<souther.compiler.coverage.CoverageSites.Site> out = new ArrayList<>();
            for (List<souther.compiler.coverage.CoverageSites.Site> occurrences
                    : byObligation().values()) {
                if (occurrences.stream().noneMatch(site -> covered.contains(site.index()))) {
                    out.add(occurrences.get(0));
                }
            }
            return List.copyOf(out);
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
            Answer<souther.compiler.check.Prepared> prepared = db.ask(new Shapes.Prepared(name));
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
            souther.compiler.query.Bodies.Elaborated checked =
                    db.ask(new Bodies.Checked(name)).value();
            Set<String> withBodies = checked == null ? Set.of() : checked.behaviorBodies().keySet();
            Map<String, Observed> byTarget = rowsOf(db, name);
            Set<Integer> lit = new LinkedHashSet<>();
            for (Observed observed : byTarget.values()) {
                for (RowOutcome row : observed.rows()) {
                    lit.addAll(litBy(row));
                }
            }

            Map<String, souther.compiler.check.PathReachability.Answers.AsRun> reachable = db.ask(new Arrived(name)).value();

            Map<String, BranchEvidence> out = new LinkedHashMap<>();
            for (Hir.BehaviorDef behavior : prepared.value().behaviors()) {
                // The arms, and not every site of the behavior. A comparison of a guard's condition
                // has a site of its own and is not a fork a row is in or out of, so counting it here
                // would report an arm the body does not have.
                List<souther.compiler.coverage.CoverageSites.Site> arms =
                        plan.arms(behavior.name());
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
         * <p>Which codes say it is each code's own answer ({@link Incompleteness.Code#leftNoRowRead}).
         * Listed here they were two, and the module whose classes could not be made was a third
         * — measured: it read as rows-all-seen, and the generator offered work for a behavior whose
         * rows nothing had read.
         */
        public boolean someRowsUnseen() {
            return incompleteness.stream().anyMatch(gap -> gap.code().leftNoRowRead());
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
        java.util.SequencedSet<SourceId> origins = db.ask(new Front.ExampleSources(module)).value();
        Map<String, List<RowOutcome>> rows = new LinkedHashMap<>();
        Map<String, List<Incompleteness>> stopped = new LinkedHashMap<>();
        List<Incompleteness> everywhere = new ArrayList<>();
        if (origins == null) {
            return Map.of();
        }
        for (SourceId sourceId : origins) {
            Output.Examples.Of observed = db.ask(Output.Examples.asked(db, module, sourceId)).value();
            if (observed == null) {
                // The source was not evaluated at all. Which behaviors it wrote rows for is exactly
                // what cannot be read, so it counts against every one of them.
                everywhere.add(Incompleteness.ofSource(
                        Incompleteness.Code.OBSERVATION_ABSENT, sourceId));
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
    public record Filling(Generator.GenerationResult pairs, Generator.GenerationResult boundaries,
                          List<GapDisposition> gaps) {

        public static final Filling NONE = new Filling(Generator.GenerationResult.NONE,
                Generator.GenerationResult.NONE, List.of());

        public Filling {
            gaps = List.copyOf(gaps);
        }

    }

    /**
     * One gap a build refuses, and what the generator can do about it.
     *
     * <p>Held as a pair rather than as rows with the gap forgotten, because what an author needs to
     * read is which part of the shortfall was answered and which was not. A block that printed only
     * what it managed reads as though it filled everything.
     */
    public record GapDisposition(Finding gap, GenerationOutcome outcome) {}

    public record Generated(String name) implements Key<Map<String, Filling>> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, Filling>> compute(Db db) {
            Answer<souther.compiler.check.Prepared> prepared = db.ask(new Shapes.Prepared(name));
            Answer<Symbols> scope = Names.derivedSymbols(db, name);
            Answer<Map<String, Sig>> sigs = db.ask(new Bodies.Signatures(name));
            if (!prepared.present() || !scope.present() || !sigs.present()) {
                return Answer.absent();
            }
            souther.compiler.query.Bodies.Elaborated checked =
                    db.ask(new Bodies.Checked(name)).value();
            Map<String, souther.compiler.core.Core> bodies =
                    checked == null ? Map.of() : checked.behaviorBodies();
            souther.compiler.coverage.CoverageSites.Plan plan =
                    souther.compiler.coverage.CoverageSites.of(bodies);
            Map<String, Observed> byTarget = rowsOf(db, name);
            Map<String, InputDomain> readInputs = db.ask(new Inputs(name)).value();
            // What the guards above each place leave, asked once for the module and read by
            // every measure below — the same reason the reading of the input is.
            Map<String, souther.compiler.check.PathReachability.Answers> arrives =
                    db.ask(new PathReached(name)).value();
            Symbols symbols = scope.value();

            Map<String, List<BorderAssessment>> boundaries =
                    db.ask(new Boundaries(name)).value();
            // And what each behavior states about its answer, which draws lines of its own.
            Map<String, souther.compiler.check.StatedContract> declared =
                    db.ask(new Bodies.StatedContracts(name)).value();

            Map<String, List<Finding>> findings = db.ask(new Findings(name)).value();
            Map<String, PartitionEvidence> partitions = db.ask(new Coverage(name)).value();

            Map<String, Filling> out = new LinkedHashMap<>();
            FixtureReader.Construction building = constructing(db, name,
                    prepared.value().forExamples(), symbols);
            for (Hir.BehaviorDef behavior : prepared.value().behaviors()) {
                if (!(behavior instanceof Hir.SpecBehavior spec)) {
                    continue;
                }
                Sig sig = sigs.value().get(spec.name());
                if (sig == null) {
                    continue;
                }
                List<BorderAssessment> edges = boundaries == null ? List.of()
                        : boundaries.getOrDefault(spec.name(), List.of());
                Generator.GenerationResult pairs;
                try {
                    pairs = pairsFor(spec, sig, symbols, bodies.get(spec.name()), plan,
                            byTarget.getOrDefault(spec.name(), Observed.NONE), building,
                            domainOf(readInputs, spec), arrivalsOf(arrives, spec),
                            statedOf(declared, spec));
                } catch (LinkageError _) {
                    // The generated classes would not link, so nothing can be built to find out
                    // what a model admits. Saying so is not the same as saying the combinations are
                    // impossible, so none of them is reported as one.
                    //
                    // Caught around the search and not around the answer. A gap's answer is owed
                    // whatever the search did, and a failure that skipped the walk over the findings
                    // would take the gaps out of a list that is meant to hold every one of them —
                    // which is the same defect the list was written against, arriving as control
                    // flow rather than as a value.
                    pairs = new Generator.GenerationResult(List.of(), List.of(),
                            List.of(new souther.compiler.partition.GenerationReason
                                    .LinkageFailed(spec.name())));
                }
                out.put(spec.name(), new Filling(pairs, offered(spec.name(), edges),
                        dispositions(findings == null ? List.of()
                                        : findings.getOrDefault(spec.name(), List.of()),
                                edges, partitions == null ? null : partitions.get(spec.name()),
                                pairs, spec)));
            }
            // In the order the module declares them, because the block printed from this is read
            // against the one before it.
            return Answer.of(Ordered.map(out));
        }

        /**
         * What the generator can do about each gap a build refuses, and about every one of them.
         *
         * <p>Walked over the findings rather than over the strategies, which is the whole of it. A
         * walk over the strategies answers for the gaps somebody wrote a strategy for and leaves the
         * rest unmentioned, and a block that says nothing about a gap it printed two lines above reads
         * as though it had filled everything.
         *
         * <p>Which answer a gap gets is decided by whether a strategy takes gaps of that kind, and
         * never by what a search came back with. The kinds are listed one at a time so that a kind
         * added later does not compile until somebody has said which of the three it is.
         */
        private static List<GapDisposition> dispositions(List<Finding> findings,
                                                      List<BorderAssessment> edges,
                                                      PartitionEvidence partition,
                                                      Generator.GenerationResult pairs,
                                                      Hir.SpecBehavior spec) {
            List<GapDisposition> out = new ArrayList<>();
            for (Finding gap : findings) {
                if (!gap.isAdequacyGap()) {
                    continue;
                }
                out.add(new GapDisposition(gap, switch (gap.about()) {
                    case About.APointOfABorder(var point) -> atEdge(gap, point);
                    case About.ACaseNoRowAppliesItTo(var input, var missing) ->
                            atCase(input, missing, partition, pairs, spec);
                    case About.AnArmNoRowGoesThrough _ -> new GenerationOutcome.NotSupported(
                            GenerationOutcome.NotSupported.Reason.NO_STRATEGY_FOR_AN_ARM);
                    case About.ACaseNoRowExpects _ -> new GenerationOutcome.NotSupported(
                            GenerationOutcome.NotSupported.Reason.NO_STRATEGY_FOR_AN_OUTPUT_CASE);
                    // Not gaps a build refuses, and the loop above does not reach them. Listed so
                    // that the switch stays exhaustive over what a finding can be about rather than
                    // over the ones thought of here.
                    case About.ACaseNothingWasSeenToProduce _, About.AClassNoRowIsIn _,
                            About.APositionNoLineDivides _, About.APositionThisCouldNotRead _, About.ARuleThisCouldNotRead _,
                            About.APositionWhoseRulesWereNotReached _,
                            About.APositionReadWiderThanItsRules _,
                            About.AQuestionNothingAnswered _,
                            About.APositionPastTheAxisLimit _ ->
                            throw new IllegalStateException("not a gap a build refuses: " + gap);
                }));
            }
            return out;
        }

        /**
         * The edge's own attempt, read off what the assessment already made.
         *
         * <p>Nothing is built here, and nothing is worked out from the verdict either. The attempt
         * says what happened; this reads it. Reading it back off {@link BorderAssessment#writability()}
         * would lose the case that matters most to an author — an edge the projection proves is
         * writable and the search could not produce a row for — which came out as a verdict of
         * "provable" with nothing said about the row that never appeared.
         *
         * <p>The assessment is the finding's own, not one looked up beside it. A gap used to carry a
         * copy of the axis, the value, the rule and the role, and this matched that copy back
         * against what {@link Boundaries} answered to find the item it had been made from — three
         * fields deep, because several rules can draw a line at one value and one border owes rows
         * at four points, so anything less answered a gap with whichever assessment came first.
         * There is nothing to match and nothing for the two readings to disagree about.
         */
        private static GenerationOutcome atEdge(Finding gap, BorderAssessment.Point point) {
            if (!point.role().againstTheLine()) {
                // A point away from the line is reported under no code and is not a gap. Reaching
                // this is the disposition of a finding and the role disagreeing about one point.
                throw new IllegalStateException("not a gap a build refuses: " + gap);
            }
            String subject = point.border().axis() + " = " + point.against();
            if (!(point.item() instanceof ItemAssessment.Owed owed)) {
                // A gap was found at a point nobody is owed a row at, which is the finding and
                // the assessment disagreeing about the same border rather than a row that could
                // not be generated.
                throw new IllegalStateException("a gap at a point nothing owes: " + gap);
            }
            return switch (owed.attempt()) {
                case ItemAssessment.Attempt.Built built ->
                        new GenerationOutcome.Generated(List.of(built.row()));
                case ItemAssessment.Attempt.Unresolved why ->
                        new GenerationOutcome.CannotGenerate(why.why());
                // Carried apart, because the assessment kept them apart. Classes that were not
                // there and classes that would not link are two things this saw, and choosing
                // one of them to print is this compiler deciding what it observed.
                //
                // The other two reasons do not reach an unmet edge: a row is already at the
                // value, or the line was never measured against the rows, and neither is a gap.
                // Where one arrives, the assessment and the finding disagree about the same
                // measurement, which is not something about generating a row.
                case ItemAssessment.Attempt.NotAttempted absent -> switch (absent.reason()) {
                    case NO_CLASSES -> new GenerationOutcome.CannotGenerate(
                            new Generator.UnresolvedCombination(List.of(subject),
                                    Generator.UnresolvedCombination.Reason
                                            .NOTHING_TO_BUILD_AGAINST));
                    case LINKAGE_FAILED -> new GenerationOutcome.CannotGenerate(
                            new Generator.UnresolvedCombination(List.of(subject),
                                    Generator.UnresolvedCombination.Reason.LINKAGE_FAILED));
                    case A_ROW_IS_ALREADY_THERE, NOT_MEASURED ->
                            throw new IllegalStateException("the assessment at " + subject
                                    + " says " + absent.reason() + ", which is not a gap: "
                                    + gap);
                };
            };
        }

        /**
         * What the axes can do about a case of an input no row applies the behavior to.
         *
         * <p>The strategy that would reach it divides the position into classes and writes a row in
         * each, so it applies exactly where an axis was derived at the position and holds this case
         * among its classes. Where none was, nothing takes the gap — and that is read off the axes
         * rather than off an empty row list, which would be the same as calling a search that found
         * nothing a fact about the model.
         */
        private static GenerationOutcome atCase(InputCaseEvidence input, TypeSymbol case_,
                                                PartitionEvidence partition,
                                                Generator.GenerationResult pairs,
                                                Hir.SpecBehavior spec) {
            String missing = case_.name();
            int at = input.at();
            String parameter = at >= 0 && at < spec.params().size()
                    ? spec.params().get(at).name() : null;
            boolean divided = partition != null && parameter != null
                    && partition.axes().stream().anyMatch(
                            axis -> axis.path().equals(parameter) && axis.classes().contains(missing));
            if (!divided) {
                return new GenerationOutcome.NotSupported(
                        GenerationOutcome.NotSupported.Reason.NO_AXIS_AT_THIS_POSITION);
            }
            String label = parameter + "=" + missing;
            List<Generator.GeneratedRow> written = pairs.rows().stream()
                    .filter(row -> row.classes().contains(label)).toList();
            if (!written.isEmpty()) {
                return new GenerationOutcome.Generated(written);
            }
            // Asked before the row list is read, because a search with nothing to put a candidate
            // through wrote nothing at every class, and a reason taken from the empty result it left
            // would name the one thing that did not happen. Which of the two it was is carried as
            // the search recorded it.
            for (souther.compiler.partition.GenerationReason why : pairs.reasons()) {
                Generator.UnresolvedCombination.Reason said = switch (why) {
                    case souther.compiler.partition.GenerationReason.NothingToBuildAgainst _ ->
                            Generator.UnresolvedCombination.Reason.NOTHING_TO_BUILD_AGAINST;
                    case souther.compiler.partition.GenerationReason.LinkageFailed _ ->
                            Generator.UnresolvedCombination.Reason.LINKAGE_FAILED;
                    // Reasons about this search rather than about there being nothing to search
                    // with. They are said in their own words elsewhere and answer nothing here.
                    case souther.compiler.partition.GenerationReason.PositionWithheld _,
                            souther.compiler.partition.GenerationReason.SearchLimit _,
                            souther.compiler.partition.GenerationReason.RowsNotRead _ -> null;
                };
                if (said != null) {
                    return new GenerationOutcome.CannotGenerate(
                            new Generator.UnresolvedCombination(List.of(label), said));
                }
            }
            return pairs.unresolved().stream()
                    .filter(left -> left.classes().contains(label))
                    .<GenerationOutcome>map(GenerationOutcome.CannotGenerate::new)
                    .findFirst()
                    // The axis was derived, so a strategy takes this class; it wrote neither a row
                    // nor a reason. What that leaves is a gap nothing here can account for, and the
                    // one thing not to do is name a cause from the shape of the emptiness.
                    .orElseGet(() -> new GenerationOutcome.CannotGenerate(
                            new Generator.UnresolvedCombination(List.of(label),
                                    Generator.UnresolvedCombination.Reason.NO_REASON_RECORDED)));
        }

        /**
         * What the edge strategy composed, read off what the boundary assessment already tried.
         *
         * <p>Its own answer and not the dispositions': a line is measured against the rows, and a
         * behavior no row names has no gap at any of its lines while every one of them is still a
         * row worth offering. Keying what is offered on what a build refuses would leave a model
         * with no rows at all — the one an author most wants rows for — with nothing.
         */
        private static Generator.GenerationResult offered(String behavior,
                                                          List<BorderAssessment> boundaries) {
            List<Generator.GeneratedRow> rows = new ArrayList<>();
            List<Generator.UnresolvedCombination> unresolved = new ArrayList<>();
            List<souther.compiler.partition.GenerationReason> stopped = new ArrayList<>();
            for (BorderAssessment border : boundaries) {
              for (souther.compiler.partition.PointRole role
                      : souther.compiler.partition.PointRole.values()) {
                if (!(border.at(role) instanceof ItemAssessment.Owed each)) {
                    continue;   // nothing is owed here, so nothing was tried and nothing is offered
                }
                switch (each.attempt()) {
                    case ItemAssessment.Attempt.Built built -> rows.add(built.row());
                    case ItemAssessment.Attempt.Unresolved why -> unresolved.add(why.why());
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
                    case ItemAssessment.Attempt.NotAttempted absent -> {
                        switch (absent.reason()) {
                            case NO_CLASSES -> stopped.add(
                                    new souther.compiler.partition.GenerationReason
                                            .NothingToBuildAgainst(behavior));
                            case LINKAGE_FAILED -> stopped.add(
                                    new souther.compiler.partition.GenerationReason
                                            .LinkageFailed(behavior));
                            case A_ROW_IS_ALREADY_THERE, NOT_MEASURED -> { }
                        }
                    }
                }
              }
            }
            return new Generator.GenerationResult(rows, unresolved,
                    stopped.stream().distinct().toList());
        }

        private static Generator.GenerationResult pairsFor(
                Hir.SpecBehavior spec, Sig sig, Symbols symbols, souther.compiler.core.Core body,
                souther.compiler.coverage.CoverageSites.Plan plan, Observed observed,
                FixtureReader.Construction building, InputDomain domain,
                souther.compiler.check.PathReachability.Answers arrives,
                souther.compiler.check.StatedContract stated) {
            if (observed.someRowsUnseen()) {
                // Rows exist that nothing read. What they cover is unknown, so what is left uncovered
                // is unknown too — and a generated row is a specific piece of work handed to a person,
                // which may already be sitting in the file that could not be evaluated.
                return new Generator.GenerationResult(List.of(), List.of(),
                        List.of(new souther.compiler.partition.GenerationReason.RowsNotRead(
                                spec.name(), observed.incompleteness())));
            }
            List<RowOutcome> rows = observed.rows();
            List<String> parameters = spec.params().stream().map(Hir.Param::name).toList();
            // One reading of what the behavior takes, for both halves of this: the rows already
            // written are read by it, and the rows offered are generated from it.
            souther.compiler.partition.BehaviorInputs inputs =
                    new souther.compiler.partition.BehaviorInputs(parameters, sig.inputTypes(),
                            symbols);
            souther.compiler.partition.Partitions.Partitioning partitioning =
                    Coverages.partitioningOf(spec, domain, sig, symbols, body, plan, arrives,
                            stated);
            Generator.Subject subject = new Generator.Subject(inputs, partitioning.axes());
            Generator.CandidateCheck check = building == null ? Generator.CandidateCheck.ANY
                    : (at, candidate) -> building.refuse(sig.ins().get(at), candidate.value());

            List<Map<AxisId, Classification>> existing = rows.stream()
                    .map(row -> RowClasses.of(row, inputs, partitioning.axes())).toList();
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
    static FixtureReader.Construction constructing(Db db, String module, souther.compiler.check.Prepared.ExampleExecution written,
                                                   Symbols symbols) {
        // The classes alone: building a value applies no behavior, so what the compile implemented is
        // not a question this asks.
        souther.compiler.generated.EvaluationArtifact artifact =
                db.ask(new Output.EvaluationLinked(module, coverageAsked(db))).value();
        Map<String, List<BehaviorRequirement>> requirements =
                db.ask(new Bodies.Requirements(module)).value();
        if (artifact == null || requirements == null) {
            return null;
        }
        Map<String, byte[]> classes = artifact.classes();
        Map<String, Hir.FnDef> values = db.ask(new Bodies.ModuleDefinitions(module)).value();
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
        /** A case some row expects and nothing was seen to produce. Said only of a behavior some row
         *  saw answer with a case: where nothing was observed at all, this is true of every case and
         *  is what the rows say of themselves. */
        OUTPUT_CASE_UNVERIFIED(null, false),
        /** A class of an axis no row is in. */
        AXIS_CLASS_UNCOVERED(null, false),
        /**
         * A point away from a border that no row is at — the {@code IN} or the {@code OUT} point.
         *
         * <p>Beside {@link #BOUNDARY_UNMET} rather than among its findings, and the difference is
         * which criterion a build is held to. A row on the line and a row one step over are what
         * simplified domain coverage asks for, and a build can be told to refuse over them. A row
         * well inside and a row well outside are the two further items reliable domain coverage adds,
         * and this reports them without naming either criterion as the bar — which is what a report
         * that claims no coverage criterion has to do.
         *
         * <p>Not a measure of its own. It comes off the same assessment of the same border as the
         * points against the line, so what a build refuses over is a reading of one measurement and
         * never a second one made to different rules.
         */
        DOMAIN_POINT_UNCOVERED(null, false),
        /**
         * A position the model draws no line through.
         *
         * <p>A fact about the model, and only said where the derivation ran to the end and found
         * nothing. A position this could not read is {@link #PARTITION_NOT_READ}: the two were one
         * finding, and the sentence this one prints was told to authors whose own body compared the
         * position two lines above.
         */
        PARTITION_NOT_DERIVABLE(null, false),
        /** A position something is written about that this did not read, with what stopped it. */
        PARTITION_NOT_READ(null, false),
        /**
         * A rule written about a position that nothing took in, and which of its questions stands.
         *
         * <p>One kind and not one per measure. What happened is that a rule raised a question and
         * nothing answered it; which section of a document a reader meets it in follows from the
         * question, and is decided where the document is written. Named for the partition, this said
         * that the fact belonged to that measure — and a rule about where the values stop would have
         * been printed under the classes, two headings away from the border it is about, which is
         * the shape of issue #842.
         *
         * <p>Not read off the borders either. A line this could not fold has no border to iterate,
         * and that is exactly when its question stands.
         *
         * <p>Told apart from {@link #PARTITION_NOT_READ} because they are different things to act
         * on. Nothing was established about a position this could not read; here the model said
         * something and no reading of it answered.
         *
         * <p>Named by the rule. A position was all a reader used to be given, which sent them
         * looking for a rule the sentence never named — and the sentence was written off one
         * reading's account of itself, so it was said of models every rule of which had been read
         * (issue #842).
         */
        RULE_UNACCOUNTED(null, false),
        /**
         * A position the axes measure whose rules the walk never reached.
         *
         * <p>Its own finding beside {@link #RULE_UNACCOUNTED}. There is no rule to name,
         * and a reader told that every rule was accounted for is told the opposite of the one thing
         * worth knowing about the position.
         */
        PARTITION_RULES_NOT_REACHED(null, false),
        /**
         * A position whose values are read from a product this reading cannot show the rules admit.
         *
         * <p>Its own finding beside the two above, and the one of the three that is not a limit an
         * author can go looking for a clause behind: every rule arrived and every rule was read.
         * What it qualifies is the classes rather than their absence, so it is said at positions the
         * axes measured as readily as at positions they did not.
         */
        PARTITION_VALUES_NOT_SEPARATED(null, false),
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
     * <p>{@code about} is what the measure established, as itself. Every reader projects it into its
     * own words; nothing here does that for them. It used to be the arguments of a message in the
     * order its key took them, which made the shape of every kind's payload follow from what four
     * of them needed for one of three readers, and left the rest carrying whatever a report happened
     * to print.
     *
     * <p>{@code kind} is derived from {@code about} rather than held beside it, so a kind and what
     * it is about cannot come apart. It is not a second thing to get right when a kind is added.
     *
     * <p>{@code status} is the measurement this came out of. A finding from a measurement that could
     * not be completed is worth printing — it says a row may be missing — and is not worth failing a
     * build over, because telling an author to write a row they may already have written is worse than
     * saying nothing.
     *
     * <p>{@code at} is a {@link souther.compiler.diag.Citation} and not a place. Most of these are
     * about a declaration this compile read, where the two are the same thing; an arm is not, being
     * one of a body that may have been spliced in from a file nobody holds. A report reading a
     * coordinate cannot tell the two apart, and printed the second as though it were the first.
     */
    public record Finding(String behavior, MeasurementStatus status, Citation at, About about) {

        /**
         * What a build does about a finding, which is what neither surface used to say.
         *
         * <p>Three answers and not two, because the question is decided by two facts. Collapsing the
         * middle one into {@link #REPORTED} would say a measure decided something it did not: a kind
         * a build refuses over, from a measurement that came to no answer, is not a gap and is not a
         * kind nobody gates on either. A report already tells that one apart in words — "undecided
         * whether a row" against "no row" — and a document that had only two words would have put
         * them under one.
         */
        public enum Disposition {
            /** A gap a build refuses over. */
            REFUSED,
            /** A kind a build refuses over, from a measurement that came to no answer. */
            UNDECIDED,
            /** Not a kind a build refuses over, whatever its measurement managed. */
            REPORTED
        }

        public Finding {
            // A finding is about somewhere. A place-less one used to become a warning with no
            // caret, which nothing produced and nothing wanted; now the reading of the citation
            // rests on there being one, so the type says so rather than the reader finding out.
            java.util.Objects.requireNonNull(at, "a finding is about a place");
            java.util.Objects.requireNonNull(about, "a finding is about something");
        }

        /**
         * Which kind of thing this is, read off what it is about.
         *
         * <p>The one place the two are related. A kind handed in beside the subject was a pair that
         * could disagree, and nothing checked it; here there is no pair. The two border kinds come
         * off one assessment of one point, and which of them a point is, is the role's answer —
         * written here rather than at the measure that found it and at every reader that sorts
         * findings, which is where the closed-border rule would otherwise be spelled three times.
         */
        public Kind kind() {
            return switch (about) {
                case About.ACaseNoRowExpects _ -> Kind.OUTPUT_CASE_UNSPECIFIED;
                case About.ACaseNothingWasSeenToProduce _ -> Kind.OUTPUT_CASE_UNVERIFIED;
                case About.ACaseNoRowAppliesItTo _ -> Kind.INPUT_CASE_UNSPECIFIED;
                case About.AClassNoRowIsIn _ -> Kind.AXIS_CLASS_UNCOVERED;
                case About.APointOfABorder(var point) -> point.role().againstTheLine()
                        ? Kind.BOUNDARY_UNMET : Kind.DOMAIN_POINT_UNCOVERED;
                case About.APositionNoLineDivides _ -> Kind.PARTITION_NOT_DERIVABLE;
                case About.ARuleThisCouldNotRead _ -> Kind.PARTITION_NOT_READ;
                // One word, whatever stopped the reading, and the reason beside it says which.
                // PARTITION_RULES_NOT_REACHED belongs to the finding above — a position the axes
                // did measure — and the two write nothing but the position, so sharing the word
                // would put two findings a reader can tell apart in the report under one a
                // consumer cannot.
                case About.APositionThisCouldNotRead _ -> Kind.PARTITION_NOT_READ;
                case About.APositionWhoseRulesWereNotReached _ ->
                        Kind.PARTITION_RULES_NOT_REACHED;
                case About.APositionReadWiderThanItsRules _ ->
                        Kind.PARTITION_VALUES_NOT_SEPARATED;
                case About.AQuestionNothingAnswered _ -> Kind.RULE_UNACCOUNTED;
                case About.APositionPastTheAxisLimit _ -> Kind.PARTITION_OMITTED;
                case About.AnArmNoRowGoesThrough _ -> Kind.ARM_UNREACHED;
            };
        }

        /**
         * What a build does about this one: the kind and the measurement behind it, together.
         *
         * <p>The one statement of it. Both surfaces of a report write this word rather than reading
         * the kinds a second time, so what a report marks and what a build refuses over cannot come
         * apart.
         */
        public Disposition disposition() {
            if (!kind().isAdequacyGap()) {
                return Disposition.REPORTED;
            }
            return status == MeasurementStatus.COMPLETE
                    ? Disposition.REFUSED : Disposition.UNDECIDED;
        }

        /** Whether this is a gap a build is entitled to refuse. */
        public boolean isAdequacyGap() {
            return disposition() == Disposition.REFUSED;
        }

        public Optional<DiagnosticCode> code() {
            return kind().code();
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
            Answer<souther.compiler.check.Prepared> prepared = db.ask(new Shapes.Prepared(name));
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
            for (Hir.BehaviorDef behavior : prepared.value().behaviors()) {
                List<Finding> found = new ArrayList<>();
                signatureFindings(behavior,
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
         *  claims — which is why these are said at {@code PARTIAL} rather than withheld until every
         *  row could be read. Which of them are said at all is each measure's own question below. */
        private static void signatureFindings(Hir.BehaviorDef behavior, SignatureEvidence signature,
                                              List<Finding> out) {
            if (signature == null || !signature.status().counted()) {
                return;
            }
            MeasurementStatus status = signature.status();
            OutputCaseEvidence output = signature.output();
            for (TypeSymbol missing : output.unspecified()) {
                out.add(new Finding(behavior.name(), status, Citation.of(behavior.pos()),
                        new About.ACaseNoRowExpects(missing)));
            }
            // Where the behavior answered for no row, every case is unverified and naming each of
            // them adds nothing to that. Asked of the rows rather than of the declaration: the two
            // agree only while the one thing that applies a behavior is the compile that generated
            // it, and a run that did apply an injected behavior would go on saying nothing about the
            // cases it was never seen to produce.
            //
            // How many rows were answered for, rather than whether any case was observed. A run whose
            // answers are of a type nothing here names observed no case and produced answers all the
            // same, and the cases it did not confirm are worth naming exactly as anywhere else.
            //
            // Left out here rather than at the printing, so that what a report shows and what a build
            // is told come from one list.
            if (output.answeredRows() > 0) {
                for (TypeSymbol missing : output.unverified()) {
                    if (!output.unspecified().contains(missing)) {
                        out.add(new Finding(behavior.name(), status, Citation.of(behavior.pos()),
                                new About.ACaseNothingWasSeenToProduce(missing)));
                    }
                }
            }
            // Walked as the evidence rather than by index: which input this is, is the evidence's
            // own answer now, so a finding is not handed a number worked out beside the list.
            for (InputCaseEvidence input : signature.inputs()) {
                for (TypeSymbol missing : input.unspecified()) {
                    out.add(new Finding(behavior.name(), status, Citation.of(behavior.pos()),
                            new About.ACaseNoRowAppliesItTo(input, missing)));
                }
            }
        }

        /** What the rows reach of what the model distinguishes. A boundary is named only where the
         *  position was read on every row: a row writing the very number the rule names, whose
         *  observation was cut short elsewhere in the same input, is not a row that missed. */
        private static void partitionFindings(Hir.BehaviorDef behavior, PartitionEvidence partition,
                                              List<Finding> out) {
            if (partition == null) {
                return;
            }
            for (PartitionEvidence.AxisCoverage axis : partition.axes()) {
                // A class nothing sits in, where nothing was measured, is not a class no row is in.
                // Stopped here rather than where the line is printed: a finding is something a measure
                // established, and one from a measure that was never made is not established at all.
                if (!axis.status().counted()) {
                    continue;
                }
                for (PartitionEvidence.AxisClass missing : axis.uncovered()) {
                    out.add(new Finding(behavior.name(), axis.status(),
                            Citation.of(behavior.pos()), new About.AClassNoRowIsIn(missing)));
                }
            }
            // The assessment's own items, walked as items. Flattened here a second way, a reader
            // that forgot a role would be short by it — which is the shape the whole measure was in
            // before a border owed its four.
            for (BorderAssessment.Point point
                    : BorderAssessment.pointsOf(partition.boundaries())) {
                // Both halves, asked of the two answers the assessment keeps apart. A point no
                // row was measured against is not a gap, and neither is one nothing has shown a
                // row can be written at — that point is where the reading stopped rather than
                // where the model does, and a row at it may be one nobody can write. A point
                // nobody is owed a row at is not a gap either, and it says so as its own shape.
                if (!point.item().isUnmetGap()) {
                    continue;
                }
                // The point itself, and one finding for either kind. Which of the two a build is
                // told about is the role's answer and is read off this where the kind is asked
                // for; the axis, the value, the rule and the role used to be copied out here, and
                // a reader then matched the copy back against the assessments to find the one it
                // came from.
                out.add(new Finding(behavior.name(), MeasurementStatus.COMPLETE,
                        Citation.of(behavior.pos()), new About.APointOfABorder(point)));
            }
            // What the model divides this position no way at all, which is the classes question and
            // is answered only for a position that has none.
            for (souther.compiler.partition.UndividedPosition position : partition.notDerivable()) {
                if (position.isAbsent()) {
                    out.add(new Finding(behavior.name(), MeasurementStatus.COMPLETE,
                            Citation.of(behavior.pos()),
                            new About.APositionNoLineDivides(position)));
                }
            }
            // And what this could not read, asked of the one reading that answers it. A position
            // with classes can still carry a statement nothing read, so this is not filtered by the
            // list above.
            for (PartitionEvidence.NotRead each : partition.notRead()) {
                // Not measured, because nothing here established anything either way about it.
                out.add(new Finding(behavior.name(), MeasurementStatus.NOT_MEASURED,
                        Citation.of(behavior.pos()),
                        switch (each) {
                            case PartitionEvidence.NotRead.ARule rule ->
                                    new About.ARuleThisCouldNotRead(rule);
                            case PartitionEvidence.NotRead.APosition position ->
                                    new About.APositionThisCouldNotRead(position);
                        }));
            }
            // And what the reading could not hold together, which is neither of the two above: no
            // rule is answerable for it and nothing went unreached. Said whatever the axes made of
            // the position, since what it qualifies is the classes and not their absence.
            for (souther.compiler.inputs.PositionValuesNotSeparated each : partition.notSeparated()) {
                out.add(new Finding(behavior.name(), MeasurementStatus.NOT_MEASURED,
                        Citation.of(behavior.pos()),
                        new About.APositionReadWiderThanItsRules(each)));
            }
            // A position the axes did measure, whose rules this reading is short of. A different
            // thing to act on from one nothing divided: the classes beside it are what the model
            // was read to say, and what was left unread may yet refuse one of them. What says how
            // much was read is what the axis carries — asked here rather than worked out a second
            // time from the lists above, which answer about rules and not about positions.
            for (PartitionEvidence.AxisCoverage axis : partition.axes()) {
                // A position the axes measure whose rules nothing looked at. Said apart from the
                // rules below: there is no rule to name, and there is no rule to name because
                // nothing was seen rather than because everything was accounted for.
                if (axis.read().reach()
                        == PartitionEvidence.AxisCoverage.Reach.SOME_OUT_OF_SIGHT) {
                    out.add(new Finding(behavior.name(), MeasurementStatus.NOT_MEASURED,
                            Citation.of(behavior.pos()),
                            new About.APositionWhoseRulesWereNotReached(axis)));
                }
            }
            // One per question a rule raised and nothing answered, whether or not the position it
            // is at came back with an axis. A rule that arrived and went unaccounted for is a fact
            // about the rule; that no axis could be derived is a fact about a measure, and the
            // second used to decide whether the first was said at all.
            for (PartitionEvidence.Unanswered each : partition.unanswered()) {
                // The question as the accounting holds it, whose own contract is that it is handed
                // on whole. Which of the names it carries a reader is shown, and what words the
                // question is put in, are the reader's — and both used to be settled here, one of
                // them only to be overruled by every surface that printed it.
                out.add(new Finding(behavior.name(), MeasurementStatus.NOT_MEASURED,
                        Citation.of(behavior.pos()),
                        new About.AQuestionNothingAnswered(each)));
            }
            for (souther.compiler.partition.Partitions.OmittedAxis dropped : partition.omitted()) {
                out.add(new Finding(behavior.name(), MeasurementStatus.COMPLETE,
                        Citation.of(behavior.pos()),
                        new About.APositionPastTheAxisLimit(dropped)));
            }
        }

        /** An arm no row goes through, at the arm and not at the declaration: what to do about it is
         *  written there. Named only where every row was read — an arm a row that never finished might
         *  have gone through is undecided, and calling it unreached sends the author after a row that
         *  exists. */
        private static void armFindings(Hir.BehaviorDef behavior, BranchEvidence branch,
                                        List<Finding> out) {
            if (branch == null || branch.status() != MeasurementStatus.COMPLETE) {
                return;
            }
            for (souther.compiler.coverage.CoverageSites.Site arm : branch.unreached()) {
                // The arm itself and not words about it. What to call one differs between a report,
                // which is written in one language, and a diagnostic, which is written in the
                // reader's — and the two readings ask the same arm rather than one of them being
                // handed the other's answer.
                out.add(new Finding(behavior.name(), branch.status(), arm.at(),
                        new About.AnArmNoRowGoesThrough(arm)));
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
            About said = finding.about();
            souther.compiler.diag.Diagnostic.Builder built = pointedAt(finding.at())
                    .say(switch (said) {
                        case About.ACaseNoRowExpects(var missing) ->
                                new ExampleMessage.NoRowExpectsThatCase(
                                        missing.name(), finding.behavior());
                        case About.ACaseNoRowAppliesItTo(var input, var missing) ->
                                new ExampleMessage.NoRowAppliesItToThatCase(missing.name(),
                                        // How a person is told which input, which is one-based and
                                        // is this sentence's to spell.
                                        String.valueOf(input.at() + 1), finding.behavior());
                        // The rule named without a place. Nothing here knows what to call a
                        // source, so a line and a column written into the sentence would be read
                        // against whichever file the reader has in mind. Where a fork of a body
                        // drew the line, the place is pointed at rather than said, and which
                        // construct it was is a phrase the catalog holds in every language.
                        //
                        // Which point of the border this is crosses that and does not replace it.
                        // How the rule is named follows from whether it has a place; which of the
                        // border's points went unmet is the measurement's own answer, and a
                        // sentence deciding one of them from the other would be reading a rule off
                        // a role.
                        case About.APointOfABorder(var point) -> againstTheLine(point).rule()
                                .wasDrawnInABodyFork()
                                ? new ExampleMessage.NoRowIsAtThePointOfTheBorderAConstructDrew(
                                        point.role().name(), point.border().axis(),
                                        point.against(), constructOf(point))
                                : new ExampleMessage.NoRowIsAtThePointOfTheBorderARuleDrew(
                                        point.role().name(), point.border().axis(),
                                        point.against(), point.border().rule().named());
                        case About.AnArmNoRowGoesThrough(var arm) ->
                                new ExampleMessage.NoRowGoesThroughThatArm(
                                        phraseFor(arm), arm.behavior());
                        // Kinds no build is told about under any code. Listed rather than
                        // defaulted, so that one added later has to be answered here rather than
                        // arriving as a warning with no sentence.
                        case About.ACaseNothingWasSeenToProduce _, About.AClassNoRowIsIn _,
                                About.APositionNoLineDivides _, About.APositionThisCouldNotRead _, About.ARuleThisCouldNotRead _,
                                About.APositionWhoseRulesWereNotReached _,
                                About.APositionReadWiderThanItsRules _,
                                About.AQuestionNothingAnswered _,
                                About.APositionPastTheAxisLimit _ ->
                                throw new IllegalArgumentException(
                                        "no message for " + finding.kind());
                    });
            switch (said) {
                case About.ACaseNoRowExpects(var missing) ->
                        built.hint(new ExampleMessage.WriteARowExpectingThatCase(missing.name()));
                case About.APointOfABorder(var point) -> {
                    // Asked of the point, and in the point's own vocabulary. A hint saying which
                    // side of the line the value falls on would be keyed on the border being closed
                    // or open rather than on the role — `n <= 100` is at its ON point on the line
                    // and `n < 100` is at its OFF point there — so it would be a second reading of
                    // one finding, sitting under a sentence that just named the role.
                    switch (point.role()) {
                        case ON -> built.hint(
                                new ExampleMessage.ARowJustInsideShowsTheBorderIsNotFurtherIn());
                        case OFF -> built.hint(
                                new ExampleMessage.ARowJustOutsideShowsTheBorderIsNotFurtherOut());
                        // Reported and warned about by nothing, which is where the two kinds part.
                        // Reaching this is a finding built for a point no diagnostic is written
                        // for, and answering it with a neighbour's hint is what that would cost.
                        case IN, OUT -> throw new IllegalStateException(
                                "only a point against the line is warned about: " + point.role());
                    }
                    // Where the rule has a place rather than a name, the place is a second region
                    // and not words in the sentence: a renderer resolves what to call its file,
                    // and a body written out of sight says so off its own coordinate.
                    //
                    // Where the guard is in a file this compile has none of, there is nothing to
                    // point at and the label says where the code came from instead. It used to be
                    // dropped, on the grounds that a label naming no source would be read against
                    // the file the diagnostic is in; a label no longer takes its file from where it
                    // is shown, so what was left unsaid can be said.
                    point.border().rule().citation().ifPresent(cited -> {
                        switch (cited) {
                            case souther.compiler.diag.Citation.Written w ->
                                    built.secondary(souther.compiler.diag.Region.point(w.at()),
                                            new ExampleMessage.TheConstructThatDrawsTheLine(
                                                    constructOf(point)));
                            case souther.compiler.diag.Citation.Reached r ->
                                    built.secondary(souther.compiler.diag.Region.point(r.at()),
                                            new ExampleMessage.TheConstructThatDrawsTheLine(
                                                    constructOf(point)));
                            // Nowhere this compilation can put a marker. Where the guard is written
                            // out of sight the label says so instead; where it is in a text the
                            // caller handed over there is no declaration to name and nothing to say,
                            // so there is no label. A marker over such a region is not an option:
                            // a place a reader is sent to names its source, and this one cannot.
                            case souther.compiler.diag.Citation.Elsewhere e ->
                                    built.secondaryOutOfSight(e.provenance(),
                                            new ExampleMessage.TheConstructThatDrawsTheLine(
                                                    constructOf(point)));
                            case souther.compiler.diag.Citation.Unplaced _ -> { }
                        }
                    });
                }
                case About.AnArmNoRowGoesThrough _ ->
                        built.hint(new ExampleMessage.EitherARowIsMissingOrNothingReachesIt());
                // The message says all there is to say. Written out rather than defaulted, for the
                // reason the switch above gives.
                case About.ACaseNoRowAppliesItTo _, About.ACaseNothingWasSeenToProduce _,
                        About.AClassNoRowIsIn _, About.APositionNoLineDivides _,
                        About.APositionThisCouldNotRead _, About.ARuleThisCouldNotRead _,
                        About.APositionWhoseRulesWereNotReached _,
                        About.APositionReadWiderThanItsRules _,
                        About.AQuestionNothingAnswered _,
                        About.APositionPastTheAxisLimit _ -> { }
            }
            return Report.of(built.build());
        }

        /**
         * Where a reader is sent for a finding: the place, or where the code was reached from when
         * it is written out of sight.
         *
         * <p>Only where to put the caret. What the warning says about that place is the body's, said
         * off the coordinate it is built at — which carries the same provenance this reads, so the
         * two cannot come apart.
         */
        static souther.compiler.diag.Diagnostic.Builder pointedAt(Citation cited) {
            return switch (cited) {
                case Citation.Written written -> souther.compiler.diag.Diagnostic.at(written.at());
                case Citation.Unplaced unplaced ->
                        souther.compiler.diag.Diagnostic.at(unplaced.at());
                case Citation.Reached reached -> souther.compiler.diag.Diagnostic.at(reached.at());
                case Citation.UnplacedElsewhere out -> souther.compiler.diag.Diagnostic.at(out.at());
                // Nowhere to point, and which module wrote the code is known. Said as that rather
                // than as no place at all: the reading that moves a report to where a reader can be
                // sent needs the answer this finding already has, and would otherwise work it out
                // again from whichever module the report was filed under.
                case Citation.OutOfSight out ->
                        souther.compiler.diag.Diagnostic.atCodeWrittenOutOfSight(out.provenance());
            };
        }

        /**
         * The border a build is warned about, which is the one a row is owed against the line.
         *
         * <p>A build is told about a point away from the line under no code at all, so one reaching
         * a warning is {@link Finding#isAdequacyGap()} and the role disagreeing about the same
         * point. Asked rather than assumed, since what decides it lives on the role and this is the
         * one place that would go on printing a boundary sentence about the other two points.
         */
        private static BorderAssessment againstTheLine(BorderAssessment.Point point) {
            if (!point.role().againstTheLine()) {
                throw new IllegalArgumentException(
                        "no build is warned about the " + point.role() + " point: " + point);
            }
            return point.border();
        }

        /** Which construct of the language drew a boundary's line, as a phrase the reader's
         *  language supplies. Asked of the rule, which is where the source's own answer is. */
        private static souther.compiler.diag.Localizable constructOf(
                BorderAssessment.Point point) {
            return point.border().rule().constructThatDrewIt().said();
        }

        /**
         * What a sentence calls one arm, as a phrase the catalog holds in every language.
         *
         * <p>Chosen here and not where the arm was found. The measurement answers what the arm is —
         * a construct and a way through it — and what to call one is a question only a sentence with
         * a reader has; the report writes a short word for the same arm and this writes a phrase, and
         * neither is the other's to decide. Written off the name the pair already settles, so a
         * construct added to the language arrives here as a case with no phrase rather than as one
         * quietly answered with a neighbour's.
         */
        private static souther.compiler.diag.Localizable phraseFor(
                souther.compiler.coverage.CoverageSites.Site arm) {
            return switch (arm.name()) {
                case THEN -> souther.compiler.diag.Localizable.of("arm.then");
                case ELSE -> souther.compiler.diag.Localizable.of("arm.else");
                case CONTINUED -> souther.compiler.diag.Localizable.of("arm.continued");
                case KEPT -> souther.compiler.diag.Localizable.of("arm.kept");
                case DROPPED -> souther.compiler.diag.Localizable.of("arm.dropped");
                case CONSTRUCTED -> souther.compiler.diag.Localizable.of("arm.constructed");
                case CASE -> souther.compiler.diag.Localizable.of("arm.case", casesOf(arm));
                case DEPARTURE -> clauseOf(arm)
                        .map(c -> souther.compiler.diag.Localizable.of("arm.departure.clause", c))
                        .orElseGet(() -> souther.compiler.diag.Localizable.of("arm.departure"));
                // Not an arm, so no warning is about one. Reaching this is the branch measure and
                // this sentence disagreeing about what it counts.
                case COMPARISON -> throw new IllegalStateException(
                        "no arm was unreached here: " + arm);
            };
        }

        private static String casesOf(souther.compiler.coverage.CoverageSites.Site arm) {
            return arm.outcome() instanceof souther.compiler.coverage.SourceOutcome.Matched matched
                    ? matched.cases().stream()
                            .map(souther.compiler.types.TypeSymbol::name)
                            .collect(java.util.stream.Collectors.joining(" | "))
                    : "";
        }

        private static java.util.Optional<String> clauseOf(
                souther.compiler.coverage.CoverageSites.Site arm) {
            return arm.outcome() instanceof souther.compiler.coverage.SourceOutcome.Failed(
                    souther.compiler.coverage.SourceOutcome.FailedBy.Construction(var clause))
                    ? clause : java.util.Optional.empty();
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
     * The cases an input position has to be covered at: what it divides into, read through the names
     * it writes its values under.
     *
     * <p>A position typed as one data has one case, and covering it is not a question: any row at all
     * covers it, so reporting {@code 1/1} everywhere adds a number that is never anything else. What
     * is worth counting is a position that can be more than one thing — which a
     * {@code data DecisionN = Decision} is, since its values are the cases of {@code Decision} under a
     * name. Asked of the written type, that name is where the reading stops, and a position the
     * declaration divides two ways comes back as one the model divides no way.
     *
     * <p>The names come off by {@link TypeOps#base}, and what a row wrote at the position has the same
     * ones taken off it ({@link FixtureReader#caseUnder}) — the terminal and the layers of the one walk
     * that says how far a newtype reaches, so neither end decides for itself how far that is.
     *
     * <p>Both ends or neither. A denominator read through the names has no member in common with a
     * numerator answering with the outermost of them, so every row would land outside the set it is
     * counted in: {@code 1} of {@code 2} covered, and both of the two still owed a row.
     */
    private static Set<TypeSymbol> inputCoverableCases(Type t, Symbols symbols) {
        return casesOfSum(TypeOps.base(t, symbols), symbols);
    }

    /**
     * The cases of an input the rules refuse, which are the ones no row can be written at.
     *
     * <p>Asked of the reading, case by case and by the declaration each case is. Only a refusal
     * takes a case out: a case the reading could not settle stays counted, because what would take
     * it out is a proof and not the absence of one — and a case counted where the reading was set
     * aside is exactly the case nobody could have proven anything about.
     *
     * <p>Nothing a body says reaches this. An {@code unreachable} arm is a claim about the same
     * position, checked against this reading rather than read into it.
     */
    private static Set<TypeSymbol> refusedAt(InputDomain read, String parameter,
                                             Set<TypeSymbol> declared) {
        if (parameter == null || declared.isEmpty()) {
            return Set.of();
        }
        souther.compiler.inputs.Position at = read.at(TermPath.of(parameter));
        if (at == null) {
            return Set.of();   // nothing was read about the position, so nothing is proven about it
        }
        return declared.stream()
                .filter(each -> at.admissionOf(each) instanceof souther.compiler.inputs.Admits.Refused)
                .collect(java.util.stream.Collectors.toCollection(LinkedHashSet::new));
    }

    /**
     * The cases the output has to be covered at, which is not quite what a row's expected arm is held
     * against ({@link TypeOps#outputCases}).
     *
     * <p>Not {@link #inputCoverableCases}. The two were one function on the strength of running the
     * same way, and they are not the same question: an output written under a name is answered with
     * that name — the arm a row states, the arm a result is read as, and the set the two are held
     * against all say {@code DecisionN} — so counting its cases here would name arms no row may write.
     * What a name over a sum means at an output is a question of its own and is not answered here.
     *
     * <p>The arm check is wider than this on purpose: it uses the single name of a position that is
     * not a sum at all to catch a row that wrote the wrong one.
     */
    private static Set<TypeSymbol> outputCoverableCases(Type t, Symbols symbols) {
        return casesOfSum(t, symbols);
    }

    /** What a sum divides into, and nothing for a type that is not one. The one thing the two
     *  measures above share; what tells them apart is which type each hands it. */
    private static Set<TypeSymbol> casesOfSum(Type t, Symbols symbols) {
        return TypeOps.isSumType(t, symbols) ? TypeOps.leafCases(t, symbols) : Set.of();
    }

    /**
     * @param parameters the behavior's parameter names, which is how a position this counts is found
     *                   in the reading of the behavior's input
     * @param read       what can arrive at each position of the input, which is what decides the
     *                   denominator here. Not the type's cases alone: a case the rules refuse is one
     *                   no row can be built at, and counting it holds the model short for ever
     */
    static SignatureEvidence evidenceOf(Sig sig, Symbols symbols, Observed seen,
                                        List<String> parameters, InputDomain read,
                                        souther.compiler.core.Core body,
                                        souther.compiler.coverage.CoverageSites.Plan plan,
                                        souther.compiler.check.PathReachability.Answers.AsRun reachable) {
        List<RowOutcome> rows = seen.rows();
        // The cases the output type has, less the ones only an arm nothing reaches produces. A case
        // no reachable producer answers with is not a gap in the rows.
        Set<TypeSymbol> declaredOut = souther.compiler.partition.ProducedCases.of(
                body, plan, reachable.answers(), outputCoverableCases(sig.outputType(), symbols));
        Set<TypeSymbol> specified = new LinkedHashSet<>();
        Set<TypeSymbol> observed = new LinkedHashSet<>();
        Set<TypeSymbol> verified = new LinkedHashSet<>();
        int unreadableOut = 0;
        int answered = 0;

        List<Type> ins = sig.inputTypes();
        List<Set<TypeSymbol>> declaredIn = new ArrayList<>(ins.size());
        List<Set<TypeSymbol>> inSpecified = new ArrayList<>(ins.size());
        List<Set<TypeSymbol>> inExecuted = new ArrayList<>(ins.size());
        List<Set<TypeSymbol>> inVerified = new ArrayList<>(ins.size());
        List<Set<TypeSymbol>> inExcluded = new ArrayList<>(ins.size());
        int[] unreadableIn = new int[ins.size()];
        for (int i = 0; i < ins.size(); i++) {
            Set<TypeSymbol> declared = inputCoverableCases(ins.get(i), symbols);
            declaredIn.add(declared);
            inSpecified.add(new LinkedHashSet<>());
            inExecuted.add(new LinkedHashSet<>());
            inVerified.add(new LinkedHashSet<>());
            inExcluded.add(refusedAt(read, i < parameters.size() ? parameters.get(i) : null,
                    declared));
        }

        for (RowOutcome row : rows) {
            boolean held = row.disposition() == Disposition.HELD;
            if (row.expectedArm() != null) {
                specified.add(row.expectedArm());
            } else if (!declaredOut.isEmpty()) {
                unreadableOut++;   // an expectation whose case the text does not say
            }
            if (row.answered()) {
                answered++;
            }
            if (row.observed()) {
                observed.add(row.resultArm());
                if (held) {
                    verified.add(row.resultArm());
                }
            }
            for (int i = 0; i < ins.size(); i++) {
                if (declaredIn.get(i).isEmpty()) {
                    continue;   // not a sum: nothing to cover at this position
                }
                TypeSymbol written = i < row.inputCases().size() ? row.inputCases().get(i) : null;
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
                : new OutputCaseEvidence(declaredOut, specified, observed, verified, unreadableOut,
                        answered);
        List<InputCaseEvidence> inputs = new ArrayList<>(ins.size());
        boolean partial = output.status() == MeasurementStatus.PARTIAL;
        for (int i = 0; i < ins.size(); i++) {
            InputCaseEvidence evidence = declaredIn.get(i).isEmpty() ? InputCaseEvidence.none(i)
                    : new InputCaseEvidence(i, declaredIn.get(i), inSpecified.get(i),
                            inExecuted.get(i), inVerified.get(i), inExcluded.get(i),
                            unreadableIn[i]);
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
        // Asked before the rows are, because it is not about them. A signature with no sum anywhere
        // in it has nothing for this measure to be about, and writing every row anybody could write
        // would not give it one — so it is inapplicable rather than unmeasured, and a build is not
        // told to go and do something about it.
        if (output.declared().isEmpty()
                && inputs.stream().allMatch(in -> in.declared().isEmpty())) {
            return SignatureEvidence.unavailable(output, inputs, SignatureEvidence.Reason.NOT_A_SUM);
        }
        if (rows.isEmpty() && seen.complete()) {
            return SignatureEvidence.unavailable(output, inputs, SignatureEvidence.Reason.NO_ROWS);
        }
        return new SignatureEvidence(output, inputs,
                partial ? MeasurementStatus.PARTIAL : MeasurementStatus.COMPLETE, null);
    }

    private Adequacy() {}

    /**
     * The sites a row is known to have gone through.
     *
     * <p>Read as a {@code switch} so that a counting this does not know about is a compile error
     * here rather than a row silently counted as having lit nothing. A row whose counting was never
     * read lights none that anything here can name, and that it was left undecided is said where the
     * row is reported.
     */
    private static java.util.Set<Integer> litBy(RowOutcome row) {
        return switch (row.run().counting()) {
            case Counting.Read read -> read.hits();
            case Counting.Unread _ -> java.util.Set.of();
        };
    }

}
