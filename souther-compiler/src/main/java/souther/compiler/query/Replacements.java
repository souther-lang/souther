package souther.compiler.query;

import souther.compiler.check.CheckSurface;
import souther.compiler.check.PathReachability;
import souther.compiler.check.Sig;
import souther.compiler.coverage.ArmReplacements;
import souther.compiler.coverage.ControlPlace;
import souther.compiler.generated.EvaluationArtifact;
import souther.compiler.generated.ProbeImage;
import souther.compiler.observe.ArmObservation;
import souther.compiler.coverage.SiteNumbering;
import souther.compiler.observe.Comparisons;
import souther.compiler.observe.Expectation;
import souther.compiler.observe.ObservedValue;
import souther.compiler.observe.Position;
import souther.compiler.observe.RowOutcome;
import souther.compiler.observe.ValueTypes;
import souther.compiler.observe.Verdict;
import souther.compiler.partition.BodyReading;
import souther.compiler.partition.FillResult;
import souther.compiler.partition.GenerationPlan;
import souther.compiler.partition.Replacement;
import souther.compiler.partition.ReplacementDisposition;
import souther.compiler.partition.ReplacementOwed;
import souther.compiler.partition.FixtureTemplate;
import souther.compiler.partition.RewriteSearch;
import souther.compiler.reach.Reachability;

import java.util.ArrayList;
import java.util.EnumSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;
import java.util.function.Predicate;

/**
 * The rewrites of each behavior's body and whether its rows tell them from the body: what the
 * written rows came to, what a search for a row the rewrite answers differently on came to where the
 * written rows said nothing, and the measure the two make.
 *
 * <p>Three questions and not one, because they are asked of different things. What the written rows
 * came to is read off their runs and needs nothing composed. A search composes rows and runs them,
 * which is the generation's work and is asked only where the written rows leave a rewrite open. The
 * measure reads both, and reads neither the account nor what a generation offers — so a finding of
 * this measure is never what decided which rows a search was asked for.
 */
public final class Replacements {

    /** What each behavior's written rows came to about each rewrite of its body. */
    public record Readings(String name)
            implements Key<Map<String, List<ReplacementReading.Account>>> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, List<ReplacementReading.Account>>> compute(Db db) {
            Answer<CheckSurface> prepared = db.ask(new Shapes.CheckSurface(name));
            Answer<Map<String, Sig>> sigs = db.ask(new Bodies.Signatures(name));
            Map<String, Adequacy.RowReading> byTarget =
                    db.ask(new Adequacy.RowReadings(name)).value();
            Bodies.Elaborated checked = db.ask(new Bodies.Observable(name)).value();
            if (!prepared.present() || !sigs.present() || byTarget == null || checked == null) {
                return Answer.absent();
            }
            // What being the same value is, read with every declaration a row's answer can be of —
            // the same reading a comparison with a row makes.
            ValueTypes types = ValueTypes.over(ExampleExecutions.checkedFieldTypes(db));
            Optional<SiteNumbering> numbering =
                    Optional.of(SiteNumbering.of(checked.numberingIdentity()));
            Map<String, PathReachability.Answers.AsRun> arrived =
                    db.ask(new Adequacy.Arrived(name)).value();
            // Which siblings the classes the rows ran in carry, asked only of a run that recorded
            // where the rows went: those are the classes that carry any, and asking where none
            // were run would build them for nothing.
            ArmReplacements carried = ArmReplacements.NONE;
            if (byTarget.values().stream().anyMatch(Adequacy.RowReading::recordedArms)) {
                EvaluationArtifact image = db.ask(
                        new Output.EvaluationLinked(name, ArmObservation.RECORD)).value();
                if (image != null
                        && image.probes() instanceof ProbeImage.Instrumented(var _, var held)) {
                    carried = held;
                }
            }
            ArmReplacements inTheClasses = carried;
            return Adequacy.answerEveryBehavior(prepared.value(), behavior -> {
                Sig sig = sigs.value().get(behavior.name());
                List<RowOutcome> rows =
                        Adequacy.RowReadings.readingFor(byTarget, behavior.name()).rowsSeen();
                if (sig == null) {
                    return List.of();
                }
                Position at = Position.at(sig.outputType());
                // What the model's own rules prove no run arrives at, with what the rows did taken
                // in: a row through an arm shows the proof of it wrong, and a proof shown wrong
                // closes no way.
                PathReachability.Answers.AsRun arrives = arrived == null ? null
                        : arrived.get(behavior.name());
                // Held to the plan the arms are places of before any of them is looked up: a
                // reading of another plan answers that nothing arrives at a place it never walked,
                // which here would prove a rewrite the same.
                if (arrives != null) {
                    arrives.answers().requireNumbering(checked.numberingIdentity());
                }
                Predicate<ControlPlace.Arm> unreached = arm -> arrives != null
                        && arrives.answers().at(arm) instanceof Reachability.Unreachable;
                return ReplacementReading.of(behavior.name(), checked.plan(), inTheClasses,
                        row -> Adequacy.armsSeenIn(row, numbering), unreached, rows,
                        new ReplacementReading.Comparing() {

                            @Override
                            public boolean same(ObservedValue left, ObservedValue right) {
                                return Comparisons.same(left, right, types, at);
                            }

                            @Override
                            public boolean holds(Expectation.Asserts stated,
                                                 ObservedValue answered) {
                                return Comparisons.verdict(stated, answered, types, at)
                                        instanceof Verdict.Held;
                            }
                        });
            });
        }
    }

    /**
     * What a search for a row the rewrite answers differently on came to, for one rewrite.
     *
     * @param disposition what the search came to
     * @param inputs      the row it found, as it would be written, or empty where it found none
     */
    public record Searched(ReplacementDisposition disposition, List<String> inputs) {

        public Searched {
            Objects.requireNonNull(disposition, "a search came to something");
            inputs = List.copyOf(inputs);
        }
    }

    /**
     * The rewrites of one behavior's body the written rows left open, each looked for as a row the
     * rewrite answers differently on.
     *
     * <p>Asked only of what the written rows left open: a rewrite a row already tells apart, or one
     * a row already shows answering differently, has its answer, and a search for it would be work
     * whose result nothing reads.
     */
    public record Witnesses(String name, String behavior)
            implements Key<Map<Replacement, Searched>> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<Replacement, Searched>> compute(Db db) {
            Map<String, List<ReplacementReading.Account>> read =
                    db.ask(new Readings(name)).value();
            if (read == null || !read.containsKey(behavior)) {
                return Answer.absent();
            }
            List<ReplacementOwed> open = new ArrayList<>();
            for (ReplacementReading.Account each : read.get(behavior)) {
                if (each.standing() instanceof ReplacementReading.Standing.Open(var lookFor)) {
                    open.add(lookFor);
                }
            }
            if (open.isEmpty()) {
                return Answer.of(Map.of());
            }
            Adequacy.Generated.Environment here =
                    Adequacy.Generated.Environment.of(db, name, behavior);
            if (here == null) {
                return Answer.absent();
            }
            // On the measure's behalf and under its figure: what is found here decides whether a
            // rewrite is a gap, so nothing the generation may spend stops it.
            int runs = db.ask(new Front.Adequacy()).value().measures().rewriteRuns();
            FillResult composed = here.searchedFor(GenerationPlan.of(here.subject(), List.of(),
                    List.of(), List.of(), List.of(), open,
                    new RewriteSearch(RewriteSearch.For.THE_MEASURE, runs)));
            Map<Replacement, Searched> out = new LinkedHashMap<>();
            for (ReplacementOwed each : open) {
                ReplacementDisposition came = composed.discharge().at(each);
                List<String> inputs = came instanceof ReplacementDisposition.Witnessed(var row)
                        ? composed.rowFor(row).inputs().stream().map(FixtureTemplate::text).toList()
                        : List.of();
                out.put(each.replacement(), new Searched(came, inputs));
            }
            return Answer.of(out);
        }
    }

    /** The replacement measure of every behavior of one module. */
    public record Measured(String name) implements Key<Map<String, ReplacementEvidence>> {

        @Override
        public String module() {
            return name;
        }

        @Override
        public Answer<Map<String, ReplacementEvidence>> compute(Db db) {
            Answer<CheckSurface> prepared = db.ask(new Shapes.CheckSurface(name));
            Map<String, Adequacy.RowReading> byTarget =
                    db.ask(new Adequacy.RowReadings(name)).value();
            if (!prepared.present() || byTarget == null) {
                return Answer.absent();
            }
            Bodies.Elaborated checked = db.ask(new Bodies.Observable(name)).value();
            Map<String, List<ReplacementReading.Account>> read =
                    db.ask(new Readings(name)).value();
            return Adequacy.answerEveryBehavior(prepared.value(), behavior -> {
                String named = behavior.name();
                if (prepared.value().isComposition(behavior)) {
                    return ReplacementEvidence.noBody();
                }
                switch (Adequacy.bodyReading(db, name, checked, named)) {
                    case BodyReading.NoBody _ -> {
                        return ReplacementEvidence.noBody();
                    }
                    case BodyReading.NotInElaboration _ -> {
                        return ReplacementEvidence.bodyNotInEvaluation(named);
                    }
                    case BodyReading.Read _ -> { }
                }
                Adequacy.RowReading observed =
                        Adequacy.RowReadings.readingFor(byTarget, named);
                // The rows are run again under a rewrite only where the classes that carry the
                // rewrites ran them, which is the build that asked where the rows went.
                if (!observed.recordedArms()) {
                    return ReplacementEvidence.notAsked(ReplacementEvidence.NotAsked.NOT_ASKED);
                }
                if (observed.armsUnseen()) {
                    return ReplacementEvidence.unreadable(
                            Adequacy.BranchCoverage.rowsBehind(observed));
                }
                if (observed.rowsSeen().isEmpty() && !observed.someRowsUnseen()) {
                    return ReplacementEvidence.notAsked(ReplacementEvidence.NotAsked.NO_ROWS);
                }
                List<ReplacementReading.Account> accounts =
                        read == null ? null : read.get(named);
                if (accounts == null) {
                    return ReplacementEvidence.bodyNotInEvaluation(named);
                }
                Map<Replacement, Searched> searched = accounts.stream().anyMatch(each ->
                        each.standing() instanceof ReplacementReading.Standing.Open)
                        ? db.ask(new Witnesses(name, named)).value() : Map.of();
                List<ReplacementEvidence.Rewrite> rewrites = new ArrayList<>();
                for (ReplacementReading.Account each : accounts) {
                    rewrites.add(new ReplacementEvidence.Rewrite(each.replacement(),
                            outcomeOf(each.standing(),
                                    searched == null ? null : searched.get(each.replacement()))));
                }
                return ReplacementEvidence.measured(named, rewrites,
                        Adequacy.BranchCoverage.rowsBehind(observed));
            });
        }

        /**
         * What one rewrite came to: what the written rows came to, and where they left it open,
         * what the search for a row came to.
         */
        private static ReplacementEvidence.Outcome outcomeOf(ReplacementReading.Standing standing,
                                                             Searched searched) {
            return switch (standing) {
                case ReplacementReading.Standing.Noticed(var by) ->
                        new ReplacementEvidence.Noticed(by);
                case ReplacementReading.Standing.Unnoticed(var shownBy, var lookFor) ->
                        new ReplacementEvidence.Unnoticed(
                                new ReplacementEvidence.ShownBy.AWrittenRow(shownBy), lookFor);
                case ReplacementReading.Standing.CannotBeAsked(var why) ->
                        new ReplacementEvidence.Undecided(switch (why) {
                            case TOO_LARGE -> ReplacementEvidence.Undecided.Why.TOO_LARGE;
                            case A_STATEMENT_WAS_NOT_READ ->
                                    ReplacementEvidence.Undecided.Why.A_STATEMENT_WAS_NOT_READ;
                            case A_RUN_DID_NOT_COME_BACK ->
                                    ReplacementEvidence.Undecided.Why.A_RUN_DID_NOT_COME_BACK;
                        });
                case ReplacementReading.Standing.Open(var lookFor) -> searched == null
                        ? new ReplacementEvidence.Undecided(
                                ReplacementEvidence.Undecided.Why.NOTHING_RAN)
                        : switch (searched.disposition()) {
                            case ReplacementDisposition.Witnessed _ ->
                                    new ReplacementEvidence.Unnoticed(
                                            new ReplacementEvidence.ShownBy.AComposedRow(
                                                    searched.inputs()), lookFor);
                            case ReplacementDisposition.NoneFound(var ended) ->
                                    new ReplacementEvidence.Undecided(whyNoneFound(ended));
                        };
            };
        }

        /**
         * Every way a search that found nothing ended, each said as itself: which figure a wider
         * run would have to raise is what a reader of an undecided rewrite acts on, and ranking
         * one way over another would hand them one of two.
         */
        private static Set<ReplacementEvidence.Undecided.Why> whyNoneFound(
                Set<ReplacementDisposition.Ended> ended) {
            Set<ReplacementEvidence.Undecided.Why> out =
                    EnumSet.noneOf(ReplacementEvidence.Undecided.Why.class);
            for (ReplacementDisposition.Ended each : ended) {
                out.add(switch (each) {
                    case EVERY_ROW_ANSWERED_ALIKE ->
                            ReplacementEvidence.Undecided.Why.NO_ROW_ANSWERED_DIFFERENTLY;
                    case NOTHING_WAS_COMPOSED ->
                            ReplacementEvidence.Undecided.Why.NOTHING_WAS_COMPOSED;
                    case RUNS_A_REWRITE_MAY_TAKE -> ReplacementEvidence.Undecided.Why.RUNS_SPENT;
                    case A_FIGURE_OF_THE_COMPOSING ->
                            ReplacementEvidence.Undecided.Why.A_COMPOSING_FIGURE_REACHED;
                    case A_RUN_DID_NOT_COME_BACK ->
                            ReplacementEvidence.Undecided.Why.A_RUN_DID_NOT_COME_BACK;
                    case NOTHING_RAN -> ReplacementEvidence.Undecided.Why.NOTHING_RAN;
                    // The measure's search is asked for on the measure's behalf, which no block's
                    // row limit stops ({@link RewriteSearch.For#THE_MEASURE}).
                    case ROWS_A_BLOCK_MAY_HOLD -> throw new IllegalStateException(
                            "a search for the measure stopped at the rows a block may hold");
                });
            }
            return out;
        }
    }

    private Replacements() {}
}
