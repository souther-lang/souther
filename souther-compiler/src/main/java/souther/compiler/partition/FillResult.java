package souther.compiler.partition;

import souther.compiler.reading.PathAccess;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.SequencedMap;
import java.util.SequencedSet;
import java.util.Set;

/**
 * What the generator came to, against the plan it was asked with.
 *
 * <p>One run's, or what the runs of one plan came to together — {@link #acrossRuns} makes the
 * second out of the first, and a plan searched one way is the second already.
 *
 * <p>A fill is total over its plan. Every class and every arm the plan names has an entry saying
 * what became of it, and the constructor is where that is settled — so a way out of the search that
 * writes no entry is a value nothing can build, rather than a silence a reader downstream has to
 * make something of. What such a reader used to make of it was a sentence saying the generator had
 * failed to say, which was true and was the only thing left to say.
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
 * @param plan       what this run was asked for
 * @param composed   the rows, in the order they were composed, which is the order a reader is
 *                   offered them in
 * @param unresolved what each place a row was looked for came to, said once apiece
 * @param reasons    what happened to this run as a whole, which is never an answer about one thing
 *                   the plan named
 * @param discharge  what became of each of them
 */
public record FillResult(GenerationPlan plan, SequencedMap<RowId, ComposedRow> composed,
                         List<Generator.UnresolvedCombination> unresolved,
                         List<GenerationReason> reasons, Discharge discharge) {

    public FillResult {
        composed = Ordered.copyOf(composed);
        unresolved = List.copyOf(unresolved);
        reasons = List.copyOf(reasons);
        if (!discharge.classes().keySet().equals(new LinkedHashSet<>(plan.classesOwed()))) {
            throw new IllegalStateException(
                    "the classes this run was asked for and the ones it answered for are not the"
                            + " same: asked " + plan.classesOwed()
                            + ", answered " + discharge.classes().keySet());
        }
        if (!discharge.arms().keySet().equals(new LinkedHashSet<>(plan.armsOwed()))) {
            throw new IllegalStateException(
                    "the arms this run was asked for and the ones it answered for are not the same:"
                            + " asked " + plan.armsOwed()
                            + ", answered " + discharge.arms().keySet());
        }
        // And the rows against what the answers point at, in both directions. A row nothing points
        // at is one nobody was offered — it would come out of the projection below with nothing to
        // say it is for, which is not a row — and an answer pointing at a row that is not here is
        // an obligation reported as met by a line the offer does not hold.
        Set<RowId> answered = new LinkedHashSet<>();
        for (ClassDisposition each : discharge.classes().values()) {
            if (each instanceof ClassDisposition.Built built) {
                answered.add(built.rowId());
            }
        }
        for (ArmDisposition each : discharge.arms().values()) {
            if (each instanceof ArmDisposition.Built built) {
                answered.add(built.rowId());
            }
        }
        if (!answered.equals(composed.keySet())) {
            throw new IllegalStateException(
                    "the rows this run composed and the rows its answers point at are not the same:"
                            + " composed " + composed.keySet() + ", pointed at " + answered);
        }
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
        Map<ClassOfAPosition, ClassDisposition> classes = new LinkedHashMap<>();
        for (ClassOfAPosition owed : plan.classesOwed()) {
            List<ClassDisposition> runs = new ArrayList<>();
            for (FillResult each : searched) {
                runs.add(each.discharge().at(owed));
            }
            classes.put(owed, offering(ClassDisposition.acrossRuns(runs), searched, composed,
                    named));
        }
        Map<Generator.ArmOwed, ArmDisposition> arms = new LinkedHashMap<>();
        for (Generator.ArmOwed owed : plan.armsOwed()) {
            List<ArmDisposition> runs = new ArrayList<>();
            for (FillResult each : searched) {
                runs.add(each.discharge().at(owed));
            }
            arms.put(owed, offering(ArmDisposition.acrossRuns(runs), searched, composed, named));
        }
        Set<Generator.UnresolvedCombination> unresolved = new LinkedHashSet<>();
        Set<GenerationReason> reasons = new LinkedHashSet<>();
        for (FillResult each : searched) {
            unresolved.addAll(each.unresolved());
            reasons.addAll(each.reasons());
        }
        return new FillResult(plan, composed, List.copyOf(unresolved), List.copyOf(reasons),
                new Discharge(classes, arms));
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
            case ClassDisposition.AcrossRuns.Unresolved(Generator.UnresolvedCombination why) ->
                    new ClassDisposition.Unresolved(why);
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
            case ArmDisposition.AcrossRuns.Unresolved(
                    SequencedSet<Generator.UnresolvedCombination> why) ->
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
        return new FillResult(plan, new LinkedHashMap<>(), List.of(), List.of(),
                Discharge.NOTHING);
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
        Map<ClassOfAPosition, ClassDisposition> classes = new LinkedHashMap<>();
        for (ClassOfAPosition owed : plan.classesOwed()) {
            classes.put(owed, new ClassDisposition.Unresolved(new Generator.UnresolvedCombination(
                    List.of(Generator.labelOf(plan.subject(), owed)), why)));
        }
        Map<Generator.ArmOwed, ArmDisposition> arms = new LinkedHashMap<>();
        for (Generator.ArmOwed owed : plan.armsOwed()) {
            arms.put(owed, new ArmDisposition.Unresolved(
                    List.of(new Generator.UnresolvedCombination(List.of(), why))));
        }
        return new FillResult(plan, new LinkedHashMap<>(), List.of(), reasons,
                new Discharge(classes, arms));
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
        List<Generator.GeneratedRow> out = new ArrayList<>();
        for (RowId id : composed.keySet()) {
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
        for (ClassOfAPosition owed : plan.classesOwed()) {
            if (discharge.at(owed) instanceof ClassDisposition.Built built
                    && built.rowId().equals(id)) {
                purposes.add(new Generator.Purpose.ForAClass(owed.at(), owed.classId(),
                        Generator.labelOf(plan.subject(), owed)));
            }
        }
        for (Generator.ArmOwed owed : plan.armsOwed()) {
            if (discharge.at(owed) instanceof ArmDisposition.Built built
                    && built.rowId().equals(id)) {
                // The place the row was steered to, which is the one it was built at. Where an arm
                // stands in the body more than once, the row went through one of the splices and a
                // purpose naming another would say the row does what it does not.
                purposes.add(new Generator.Purpose.ForAnArm(built.at()));
            }
        }
        return new Generator.GeneratedRow(purposes, row.inputs(), row.answers());
    }
}
