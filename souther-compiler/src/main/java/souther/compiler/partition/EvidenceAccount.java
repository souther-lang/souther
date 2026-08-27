package souther.compiler.partition;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What became of each thing the rules said, across the stage that turns it into a measure.
 *
 * <p><b>The account starts where the loss is.</b> {@link LinesRead} holds the reading that draws
 * borders to what it produced, and it is written from the axes: a piece of evidence that never
 * reached an axis is not a line that reading ever found, so nothing there could say it went
 * missing. A position whose body drew two lines on it came back reported as one whose body draws
 * none, with the measurement called complete (issue #1140). An account is worth what it is anchored
 * to, and this one is anchored to what this stage was handed.
 *
 * <p><b>Exactly one disposition each.</b> Not at least one: a piece of evidence measured at one axis
 * and left aside at another is this stage saying two things about one fact. Not at most one either —
 * that is the whole point.
 *
 * <p>What the dispositions are is not decided here. Each is written where the stage does the thing
 * it names, so an outcome added to the stage is an outcome named at the place it happens; gathered
 * here from what was left over, the name would be this account's guess about somebody else's code.
 *
 * <p>The filing that runs before this owns its own losses — a rule it could not place comes out as a
 * finding naming the rule ({@link LinesWhereTheyFall.Filed#notPlaced}), and those never reach here.
 * Each stage answers for what it was given.
 */
final class EvidenceAccount {

    /** What this stage did with one piece of evidence. */
    sealed interface Disposition {

        /** It divides an axis, which carries its cut. */
        record Measured(AxisId at) implements Disposition {}

        /**
         * It falls where the position holds no value, so it divides nothing there. Not a rule that
         * went unread: what it says was understood, and where it says it is outside the position.
         */
        record OutsideThePosition() implements Disposition {}

        /** Nothing reaches the comparison it was read from, so what it divides is nothing that
         *  gets there. */
        record NothingArrivesAtIt() implements Disposition {}

        /**
         * The declarations already measure this position at another number, and this stage does not
         * add a second measure of a position a rule of its own divides.
         *
         * <p>A policy of this stage and not a fact about the model, which is why it is said rather
         * than left out: an author is not told anything, and an account that simply had no entry
         * would be an account that cannot tell this from a loss.
         */
        record ThePositionIsAlreadyMeasured(AxisId by) implements Disposition {}
    }

    private final Set<LineEvidence.FiledOccurrence> owed = new LinkedHashSet<>();
    private final Map<LineEvidence.FiledOccurrence, Disposition> answered = new LinkedHashMap<>();

    EvidenceAccount(List<LineEvidence> evidence) {
        evidence.forEach(each -> owed.add(each.occurrence()));
    }

    void disposedOf(LineEvidence.FiledOccurrence what, Disposition how) {
        Disposition already = answered.put(what, how);
        if (already != null && !already.equals(how)) {
            throw new IllegalStateException("what became of " + what + " was said twice, as "
                    + already + " and as " + how);
        }
    }

    void measured(LineEvidence what, AxisId at) {
        disposedOf(what.occurrence(), new Disposition.Measured(at));
    }

    /**
     * That this stage said what became of everything it was handed, and that an axis it says
     * something was measured at is one it kept.
     *
     * <p><b>What this does not hold.</b> That the axis carries a cut of the rule. A line the
     * position has no value beside divides it and has no cut to be at — {@code 3 * d <= 1} cuts at
     * a third — so requiring one would call a measured line lost. What holds a border to the line it
     * was made of is {@link LinesRead}, downstream of here, and the two are anchored a stage apart
     * on purpose.
     */
    void everyPieceWasDisposedOf(List<Axis> kept) {
        Set<AxisId> there = new LinkedHashSet<>();
        kept.forEach(each -> there.add(each.id()));
        List<LineEvidence.FiledOccurrence> nowhere = answered.entrySet().stream()
                .filter(each -> each.getValue() instanceof Disposition.Measured(AxisId at)
                        && !there.contains(at))
                .map(Map.Entry::getKey).toList();
        if (!nowhere.isEmpty()) {
            throw new IllegalStateException(
                    "this stage says it measured evidence at an axis it did not keep: " + nowhere);
        }
        everyPieceWasDisposedOf();
    }

    /** That this stage said what became of everything it was handed. */
    private void everyPieceWasDisposedOf() {
        List<LineEvidence.FiledOccurrence> lost = owed.stream()
                .filter(each -> !answered.containsKey(each)).toList();
        if (!lost.isEmpty()) {
            throw new IllegalStateException(
                    "the rules said something this stage did not say what became of: " + lost
                            + " — a measure reported as complete over evidence that went missing"
                            + " is what this account exists to refuse");
        }
        List<LineEvidence.FiledOccurrence> strangers = answered.keySet().stream()
                .filter(each -> !owed.contains(each)).toList();
        if (!strangers.isEmpty()) {
            throw new IllegalStateException(
                    "this stage said what became of evidence it was not handed: " + strangers);
        }
    }
}
