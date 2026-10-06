package souther.compiler.query;

import souther.compiler.check.CheckSurface;
import souther.compiler.check.Sig;
import souther.compiler.coverage.ArmProbe;
import souther.compiler.coverage.SiteNumbering;
import souther.compiler.observe.Comparisons;
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

import java.util.ArrayList;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.Optional;
import java.util.Set;

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
            return Adequacy.answerEveryBehavior(prepared.value(), behavior -> {
                Sig sig = sigs.value().get(behavior.name());
                List<RowOutcome> rows =
                        Adequacy.RowReadings.readingFor(byTarget, behavior.name()).rowsSeen();
                if (sig == null) {
                    return List.of();
                }
                // The arms a row stating its answer went through. An arm no row reaches is owed a
                // row under its own code, and one only a row waiting for its answer reaches is too;
                // a rewrite of either is one no row could notice, and saying so would be the same
                // gap said twice.
                Set<ArmProbe> reached = new HashSet<>();
                for (RowOutcome row : rows) {
                    if (!Adequacy.awaitsItsAnswer(row)) {
                        reached.addAll(Adequacy.armsSeenIn(row, numbering));
                    }
                }
                Position at = Position.at(sig.outputType());
                return ReplacementReading.of(name, behavior.name(), checked.plan(), reached, rows,
                        new ReplacementReading.Comparing() {

                            @Override
                            public boolean same(ObservedValue left, ObservedValue right) {
                                return Comparisons.same(left, right, types, at);
                            }

                            @Override
                            public boolean holds(souther.compiler.observe.Expectation.Asserts stated,
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
            FillResult composed = here.searchedFor(GenerationPlan.of(here.subject(), List.of(),
                    List.of(), List.of(), List.of(), open));
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
                            case NOTHING_ANSWERED ->
                                    ReplacementEvidence.Undecided.Why.NOTHING_ANSWERED;
                            case A_STATEMENT_WAS_NOT_READ ->
                                    ReplacementEvidence.Undecided.Why.A_STATEMENT_WAS_NOT_READ;
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
         * The one way a search that found nothing is said to have ended. A search stopped short
         * outranks one that ran to the end, since a stop is what a wider run could go past.
         */
        private static ReplacementEvidence.Undecided.Why whyNoneFound(
                Set<ReplacementDisposition.Ended> ended) {
            if (ended.contains(ReplacementDisposition.Ended.THE_SEARCH_STOPPED)) {
                return ReplacementEvidence.Undecided.Why.THE_SEARCH_STOPPED;
            }
            if (ended.contains(ReplacementDisposition.Ended.EVERY_ROW_ANSWERED_ALIKE)) {
                return ReplacementEvidence.Undecided.Why.NO_ROW_ANSWERED_DIFFERENTLY;
            }
            if (ended.contains(ReplacementDisposition.Ended.NOTHING_WAS_COMPOSED)) {
                return ReplacementEvidence.Undecided.Why.NOTHING_WAS_COMPOSED;
            }
            return ReplacementEvidence.Undecided.Why.NOTHING_RAN;
        }
    }

    private Replacements() {}
}
