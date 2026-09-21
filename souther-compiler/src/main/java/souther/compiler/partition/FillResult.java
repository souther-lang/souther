package souther.compiler.partition;

import souther.compiler.reading.PathAccess;
import souther.compiler.values.InOneOrder;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;
import java.util.Set;

/**
 * What the generator came to, against the plan it was asked with.
 *
 * <p>One run's, or what the runs of one plan came to together — {@link #acrossRuns} makes the
 * second out of the first, and a plan searched one way is the second already.
 *
 * <p>What the plan was is {@link Discharge#plan}: a fill is total over it, and holding a plan here
 * beside a discharge free to disagree with it is the invalid value {@link Discharge}'s own
 * constructor now refuses to build. What is settled here instead is the rows against what the
 * discharge's answers point at, in both directions — a row nothing points at is one nobody was
 * offered, and an answer pointing at a row that is not here is an obligation reported as met by a
 * line the offer does not hold.
 *
 * <p>Apart from {@link Generator.GenerationResult}, which is what a generation with no plan comes
 * to. The rows offered at a behavior's boundaries are composed for points nobody was asked about
 * and nothing is owed at, and holding both in one shape meant a result that had dropped its
 * obligations and one that never had any were the same value.
 *
 * <p><b>What a row was composed for is not held here.</b> It is read back off the discharge, which
 * is the one place that says which obligation a row answered. Written down beside the row as well,
 * the two came apart: a row composed for a class and later found to take an arm was merged into one
 * line, and the class's own entry went on holding the line from before the merge.
 *
 * @param composed   the rows, in the order they were composed, which is the order a reader is
 *                   offered them in
 * @param unresolved what each place a row was looked for came to, said once apiece — the words and
 *                   what of this compiler's the search met, because a reader of this list is
 *                   reading what the class itself came to and there is no second place it is said.
 *                   A point is the other way round and keeps its figure at its own account, which
 *                   is why what reaches a reader from here and from there is not one list
 * @param reasons    what happened to this run as a whole, which is never an answer about one thing
 *                   the plan named
 * @param discharge  the plan this run was asked with and what became of each thing it named
 */
public record FillResult(SequencedMap<RowId, ComposedRow> composed,
                         List<CameToNothing> unresolved,
                         List<GenerationReason> reasons, Discharge discharge) {

    public FillResult {
        composed = Ordered.copyOf(composed);
        // Each word once, with what the searches that came back with it met added up
        // ({@link CameToNothing#joined}). A run of this plan is asked the same thing more than
        // once — the runs of one plan are folded through here — and two answers under one word
        // would reach a reader as two classes with half the figures apiece.
        unresolved = CameToNothing.joined(unresolved);
        reasons = List.copyOf(reasons);
        // The rows against what the answers point at, in both directions. A row nothing points at
        // is one nobody was offered — it would come out of the projection below with nothing to
        // say it is for, which is not a row — and an answer pointing at a row that is not here is
        // an obligation reported as met by a line the offer does not hold. Read off one switch
        // over the discharge's own answers, in the plan's order: a kind added to
        // {@link GenerationAnswer} without a case here does not compile, which is what keeps this
        // in step with what a run was actually asked for.
        Set<RowId> answered = new LinkedHashSet<>();
        for (GenerationAnswer each : discharge.inPlanOrder()) {
            switch (each) {
                case GenerationAnswer.Class(var _, ClassDisposition.Built built) ->
                        answered.add(built.rowId());
                case GenerationAnswer.Arm(var _, ArmDisposition.Built built) ->
                        answered.add(built.rowId());
                case GenerationAnswer.Pair(var _, ClassDisposition.Built built) ->
                        answered.add(built.rowId());
                case GenerationAnswer.Meeting(var _, ClassDisposition.Built built) ->
                        answered.add(built.rowId());
                default -> { }
            }
        }
        if (!answered.equals(composed.keySet())) {
            // Both sides in one order. What the answers point at is gathered by walking the
            // discharge, which holds no order of its entries, so a sentence that named them as
            // they were gathered would read two ways for one discharge.
            throw new IllegalStateException(
                    "the rows this run composed and the rows its answers point at are not the same:"
                            + " composed " + InOneOrder.of(composed.keySet())
                            + ", pointed at " + InOneOrder.of(answered));
        }
    }

    /** What this run was asked for, which is {@link Discharge#plan}. */
    public GenerationPlan plan() {
        return discharge.plan();
    }

    /**
     * What several runs over one plan came to together.
     *
     * <p>A behavior whose dependencies a way leaves open is searched once per way of standing them
     * in, and what the searches found is one answer about the model. Read off one run, the answer
     * would be about that run's stand-ins and would be reported as an answer about the model.
     *
     * <p>What the answer about the model is at each obligation is {@link
     * ClassDisposition#acrossRuns} and {@link ArmDisposition#acrossRuns}, said beside the answers a
     * run gives. This is the rest: the plan every run has to have been asked with, the reasons of
     * the runs as a whole, and the numbers the rows come out under.
     *
     * <p><b>Which row a reader is offered is settled here and nowhere above.</b> The answer about
     * the model names every run that composed one; a reader is offered one of them, which is the
     * one enumerated first. That choice is about how the rows are presented, so the answer itself
     * does not turn on the order the runs were made in and this does.
     *
     * <p><b>The rows of the runs whose obligations another run's row was named for do not go on.</b>
     * What they were searched with has been read already — it is in this answer, at every obligation
     * they reached — and offering them as well would be offering rows for what they turn out to
     * reach besides. That is a question about incidental coverage rather than about which cases
     * were searched, and nothing here is owed it.
     */
    public static FillResult acrossRuns(List<FillResult> searched) {
        if (searched.isEmpty()) {
            // A plan is searched at least once, so nothing to join is a caller with no question
            // rather than a question nothing answered. Which plan the answer would be about is the
            // first thing this needs and the one thing no run can supply.
            throw new IllegalArgumentException("no runs of a plan to join");
        }
        GenerationPlan plan = searched.getFirst().plan();
        for (FillResult each : searched) {
            // One question asked several ways, not several questions. Answers to two plans joined
            // here would be reported as one behavior's, and the obligations of one of them would be
            // answered by what was never asked about them.
            if (!each.plan().equals(plan)) {
                throw new IllegalArgumentException(
                        "runs of two plans cannot be joined: " + plan + " and " + each.plan());
            }
        }
        if (searched.size() == 1) {
            // The one run's rows keep the numbers they were composed under. Folding it would come
            // to the same answer and hand the rows different numbers, and nothing is owed the
            // second of those.
            return searched.getFirst();
        }
        SequencedMap<RowId, ComposedRow> composed = new LinkedHashMap<>();
        Map<OfARun, RowId> named = new LinkedHashMap<>();
        // Every obligation, folded by the kind it is — a kind added to {@link GenerationObligation}
        // without a case here does not compile, which is what keeps this fold in step with the
        // universe the plan closed.
        List<GenerationAnswer> answers = new ArrayList<>();
        for (GenerationObligation obligation : plan.obligations()) {
            switch (obligation) {
                case GenerationObligation.Class q -> {
                    List<ClassDisposition> runs = new ArrayList<>();
                    for (FillResult each : searched) {
                        runs.add(each.discharge().at(q.target()));
                    }
                    answers.add(new GenerationAnswer.Class(q,
                            offering(ClassDisposition.acrossRuns(runs), searched, composed, named)));
                }
                case GenerationObligation.Arm q -> {
                    List<ArmDisposition> runs = new ArrayList<>();
                    for (FillResult each : searched) {
                        runs.add(each.discharge().at(q.target()));
                    }
                    answers.add(new GenerationAnswer.Arm(q,
                            offering(ArmDisposition.acrossRuns(runs), searched, composed, named)));
                }
                // And the combinations of two classes, folded the way the classes above are: what
                // the runs came to together is one answer, and a row one of them composed keeps
                // being the row.
                case GenerationObligation.Pair q -> {
                    List<ClassDisposition> runs = new ArrayList<>();
                    for (FillResult each : searched) {
                        runs.add(each.discharge().at(q.target()));
                    }
                    answers.add(new GenerationAnswer.Pair(q,
                            offering(ClassDisposition.acrossRuns(runs), searched, composed, named)));
                }
                case GenerationObligation.Meeting q -> {
                    List<ClassDisposition> runs = new ArrayList<>();
                    for (FillResult each : searched) {
                        runs.add(each.discharge().at(q.target()));
                    }
                    answers.add(new GenerationAnswer.Meeting(q,
                            offering(ClassDisposition.acrossRuns(runs), searched, composed, named)));
                }
            }
        }
        // Every run's, in the order the runs were made, and put together where this is built: the
        // runs of one plan meet what they meet, so a word two of them came back with is one answer
        // and what each met on the way to it is the other's as much as its own. Held apart by
        // whether the whole answer was equal — which is what a set of them does — a figure one run
        // reached would be offered as a second class for a reader to act on.
        List<CameToNothing> unresolved = new ArrayList<>();
        Set<GenerationReason> reasons = new LinkedHashSet<>();
        for (FillResult each : searched) {
            unresolved.addAll(each.unresolved());
            reasons.addAll(each.reasons());
        }
        return new FillResult(composed, List.copyOf(unresolved), List.copyOf(reasons),
                Discharge.of(plan, answers));
    }

    /**
     * The answer about a class as a reader is offered it, with the row under the number it goes by
     * here.
     *
     * <p>The first of the runs that composed one. Every one of them answers the obligation, and
     * offering a second would be offering a row for what it turns out to reach besides.
     */
    private static ClassDisposition offering(ClassDisposition.AcrossRuns answer,
                                             List<FillResult> searched,
                                             SequencedMap<RowId, ComposedRow> composed,
                                             Map<OfARun, RowId> named) {
        return switch (answer) {
            case ClassDisposition.AcrossRuns.Built(List<ClassDisposition.AcrossRuns.Witness> of) -> {
                ClassDisposition.AcrossRuns.Witness first = of.getFirst();
                yield new ClassDisposition.Built(naming(searched, composed, named, first.run(),
                        first.built().rowId()));
            }
            case ClassDisposition.AcrossRuns.Unresolved(CameToNothing came) ->
                    new ClassDisposition.Unresolved(came);
        };
    }

    /**
     * The same for an arm.
     *
     * <p>The row and the place it went through are taken from the one witness. They are what one
     * run answered with, and a row of one run beside the place another run's row went through would
     * say a row goes somewhere it does not.
     */
    private static ArmDisposition offering(ArmDisposition.AcrossRuns answer,
                                           List<FillResult> searched,
                                           SequencedMap<RowId, ComposedRow> composed,
                                           Map<OfARun, RowId> named) {
        return switch (answer) {
            case ArmDisposition.AcrossRuns.Built(List<ArmDisposition.AcrossRuns.Witness> of) -> {
                ArmDisposition.AcrossRuns.Witness first = of.getFirst();
                yield new ArmDisposition.Built(naming(searched, composed, named, first.run(),
                        first.built().rowId()), first.built().at());
            }
            case ArmDisposition.AcrossRuns.Unresolved(java.util.SequencedSet<CameToNothing> why) ->
                    new ArmDisposition.Unresolved(List.copyOf(why));
            case ArmDisposition.AcrossRuns.NoWayIn(List<PathAccess> at) ->
                    new ArmDisposition.NoWayIn(at);
        };
    }

    /**
     * The number one run's row goes by among all of them, adding it to the rows this holds the
     * first time it is named.
     *
     * <p>Numbered afresh because a row id tells rows of one run apart and nothing more. Two runs
     * each number their rows from nought, and taking the numbers as they came would hold one row
     * under an id another run's row already had.
     */
    private static RowId naming(List<FillResult> searched, SequencedMap<RowId, ComposedRow> composed,
                                Map<OfARun, RowId> named, int run, RowId rowId) {
        OfARun which = new OfARun(run, rowId);
        RowId already = named.get(which);
        if (already != null) {
            return already;
        }
        RowId here = new RowId(composed.size());
        named.put(which, here);
        composed.put(here, searched.get(run).composed().get(rowId));
        return here;
    }

    /** A row of one of the runs, which is what tells two rows apart while they are being joined. */
    private record OfARun(int run, RowId rowId) {}

    /** Nothing asked for, nothing composed, nothing to answer for. */
    public static FillResult nothingAskedOf(GenerationPlan plan) {
        return new FillResult(new LinkedHashMap<>(), List.of(), List.of(),
                Discharge.nothingAskedOf(plan));
    }

    /**
     * A run that ended before it looked for anything, with every obligation told the same thing.
     *
     * <p>For the ways a generation stops without searching: the rows could not be read, the classes
     * would not link, nothing could be composed to stand in for what the behavior requires. Each of
     * those is one fact about the run, said in {@code reasons} — and each of
     * them used to be the whole of what was recorded, so a reader asking after one class or one arm
     * found nothing at all and said the generator had failed to say. The fact is the same for every
     * obligation here, which is why one word serves them all; what it is not is a reason for a
     * reader to work out from an absence.
     *
     * <p>No {@code unresolved} beside them. That list is the places a row was looked for, and this
     * is a run in which none was.
     */
    public static FillResult nothingWasLookedFor(GenerationPlan plan,
                                                 Generator.UnresolvedCombination.Reason why,
                                                 List<GenerationReason> reasons) {
        // Nothing of this compiler's was met anywhere here, because nothing was looked for. A
        // figure is what a search ran into, and there was no search.
        List<GenerationAnswer> answers = new ArrayList<>();
        for (GenerationObligation obligation : plan.obligations()) {
            switch (obligation) {
                case GenerationObligation.Class q -> answers.add(new GenerationAnswer.Class(q,
                        new ClassDisposition.Unresolved(CameToNothing.metNothing(
                                new Generator.UnresolvedCombination(
                                        List.of(Generator.labelOf(plan.subject(), q.target())),
                                        why)))));
                case GenerationObligation.Arm q -> answers.add(new GenerationAnswer.Arm(q,
                        new ArmDisposition.Unresolved(List.of(CameToNothing.metNothing(
                                new Generator.UnresolvedCombination(List.of(), why))))));
                case GenerationObligation.Pair q -> answers.add(new GenerationAnswer.Pair(q,
                        new ClassDisposition.Unresolved(CameToNothing.metNothing(
                                new Generator.UnresolvedCombination(
                                        q.target().classIdsInOrder(), why)))));
                case GenerationObligation.Meeting q -> answers.add(new GenerationAnswer.Meeting(q,
                        new ClassDisposition.Unresolved(CameToNothing.metNothing(
                                new Generator.UnresolvedCombination(List.of(), why)))));
            }
        }
        return new FillResult(new LinkedHashMap<>(), List.of(), reasons,
                Discharge.of(plan, answers));
    }

    /**
     * The rows a reader is offered, each carrying what it was composed for.
     *
     * <p>Read off the discharge rather than kept beside the row, so a row that answers two
     * obligations says so because both of them point at it.
     *
     * <p>In the plan's order, classes before arms. Which is one rule, said here: the obligations
     * are held in the order they were gathered exactly so that this order is the same twice, and
     * taking it off the discharge's own iteration would leave the purposes of one model coming out
     * however a map happened to be walked.
     */
    public List<Generator.GeneratedRow> rows() {
        // By the number each row is filed under, which is what a reader is offered them by. Taken
        // off the map as it is held, the list would be in the order the search happened to compose
        // them in — an order two equal results were built two ways, so what a reader is shown would
        // not be settled by what this result is.
        List<RowId> ids = new ArrayList<>(composed.keySet());
        ids.sort(Comparator.comparingInt(RowId::value));
        List<Generator.GeneratedRow> out = new ArrayList<>();
        for (RowId id : ids) {
            out.add(rowFor(id));
        }
        return List.copyOf(out);
    }

    /** One of them, for a reader holding an answer that points at it. */
    public Generator.GeneratedRow rowFor(RowId id) {
        ComposedRow row = composed.get(id);
        if (row == null) {
            throw new IllegalArgumentException("no row of this run is " + id);
        }
        List<Generator.Purpose> purposes = new ArrayList<>();
        // One switch over every kind the plan can hold, in the plan's order, rather than one loop
        // apiece. A kind added to {@link GenerationAnswer} without a case here does not compile,
        // which is what keeps this in step with what a run was actually asked for.
        for (GenerationAnswer each : discharge.inPlanOrder()) {
            switch (each) {
                case GenerationAnswer.Class(var obligation, ClassDisposition.Built built)
                        when built.rowId().equals(id) -> {
                    ClassOfAPosition owed = obligation.target();
                    purposes.add(new Generator.Purpose.ForAClass(owed.at(), owed.classId(),
                            Generator.labelOf(plan().subject(), owed)));
                }
                case GenerationAnswer.Arm(var _, ArmDisposition.Built built)
                        when built.rowId().equals(id) ->
                        // The place the row was steered to, which is the one it was built at. Where
                        // an arm stands in the body more than once, the row went through one of the
                        // splices and a purpose naming another would say the row does what it does
                        // not.
                        purposes.add(new Generator.Purpose.ForAnArm(built.at()));
                // And the combinations of two classes this row is in. A row composed for one may
                // sit in others, and each of them points at it here — which is what makes one row
                // the offer for as many requirements as it settles rather than one row apiece.
                case GenerationAnswer.Pair(var obligation, ClassDisposition.Built built)
                        when built.rowId().equals(id) -> {
                    ObligationIdentity.OfAFallbackPairCell owed = obligation.target();
                    purposes.add(new Generator.Purpose.ForAFallbackPairCell(owed.classes(),
                            owed.classes().stream()
                                    .map(each2 -> Generator.labelOf(plan().subject(), each2))
                                    .sorted().toList()));
                }
                // And the combinations of the body's decisions this row makes. The same rule again:
                // a row composed at one meeting may be watched making another, and each of them
                // points at it.
                case GenerationAnswer.Meeting(var obligation, ClassDisposition.Built built)
                        when built.rowId().equals(id) ->
                        purposes.add(new Generator.Purpose.ForACombinationOfDecisions(
                                obligation.target().settled()));
                default -> { }
            }
        }
        return new Generator.GeneratedRow(purposes, row.inputs(), row.answers());
    }
}
