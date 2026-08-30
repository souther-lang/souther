package souther.compiler.partition;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * What became of each thing the rules said, across the stage that turns it into a measure.
 *
 * <p><b>Anchored to what this stage is handed.</b> {@link LinesRead} holds the reading that draws
 * borders to what it produced, and it is written from the axes: a piece of evidence that never
 * reaches an axis is not a line that reading ever finds, so nothing there can say it went missing,
 * and a measure short of every line a body drew on a position reads as complete. An account is
 * worth what it is anchored to, and the two are anchored a stage apart for that reason.
 *
 * <p><b>One disposition each, and the same one however often it is said.</b> A piece of evidence
 * measured at one axis and left aside at another is this stage saying two things about one fact, and
 * it is refused where the second is said. Saying the same thing twice about one piece is one answer:
 * what this holds the stage to is that everything it was handed has an answer, and not that the
 * stage reached each piece exactly once.
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
         * The declarations already measure this position at another number, and this stage does not
         * add a second measure of a position a rule of its own divides.
         *
         * <p>A policy of this stage and not a fact about the model, which is why it is said rather
         * than left out: an author is not told anything, and an account that simply had no entry
         * would be an account that cannot tell this from a loss.
         */
        record ThePositionIsAlreadyMeasured(AxisId by) implements Disposition {}
    }

    /** One piece of evidence and what became of it, held together so that holding the stage to a
     *  {@link Disposition.Measured} can ask the evidence what it should have left behind. */
    private record Answered(LineEvidence what, Disposition how) {}

    private final Map<LineEvidence.FiledEvidenceId, LineEvidence> owed = new LinkedHashMap<>();
    private final Map<LineEvidence.FiledEvidenceId, Answered> answered = new LinkedHashMap<>();

    /**
     * The evidence this stage was handed, and the one thing about it this has to establish rather
     * than assume.
     *
     * <p><b>That the identity tells the pieces apart.</b> Everything below counts by
     * {@link LineEvidence#id}, so two pieces sharing one is one entry here — and then the piece that
     * went missing is the one the other answered for. An account whose denominator is short before
     * any work happens reports a complete measure over evidence it never held, which is the sentence
     * this whole type exists to refuse.
     *
     * <p>Checked where the input is taken and not where two of them meet. A check that fires only
     * when both arrive assumes what it is meant to establish: the case it has to catch is exactly
     * the one where the second never comes.
     *
     * <p>The same piece handed over twice is one piece. What that would say about the stage is
     * nothing, and nothing here counts arrivals.
     */
    EvidenceAccount(List<LineEvidence> evidence) {
        for (LineEvidence each : evidence) {
            LineEvidence already = owed.put(each.id(), each);
            if (already != null && !already.equals(each)) {
                throw new IllegalStateException("two pieces of evidence are called " + each.id()
                        + ": " + already + " and " + each
                        + " — an account that cannot tell them apart has one denominator for two");
            }
        }
    }

    void disposedOf(LineEvidence what, Disposition how) {
        // Held against what was handed over rather than against whatever else was disposed of. The
        // identity is one to one over the input, so a piece arriving here under an id belonging to
        // another is a piece this stage was never given.
        LineEvidence given = owed.get(what.id());
        if (given != null && !given.equals(what)) {
            throw new IllegalStateException("this stage disposed of " + what
                    + " under the name of " + given);
        }
        Answered already = answered.put(what.id(), new Answered(what, how));
        if (already != null && !already.how().equals(how)) {
            throw new IllegalStateException("what became of " + what.id()
                    + " was said twice, as " + already.how() + " and as " + how);
        }
    }

    void measured(LineEvidence what, AxisId at) {
        disposedOf(what, new Disposition.Measured(at));
    }

    /**
     * That this stage said what became of everything it was handed, and that what it says it
     * measured is on the axis it names.
     *
     * <p><b>Held to what the axis carries, and not to the word.</b> Saying a piece of evidence was
     * measured is a claim about an axis, and a claim nothing checks is what this account exists to
     * refuse one stage earlier. Each kind of evidence is looked for by its own key: a line the
     * position has a value beside leaves a cut carrying the rule, one it has no value beside leaves
     * the place the values part with the authored line against it, and a value singled out leaves a
     * cut like the first. Looked for by one key, the second would be reported lost.
     */
    void everyPieceWasDisposedOf(List<Axis> kept) {
        Map<AxisId, Axis> there = new LinkedHashMap<>();
        kept.forEach(each -> there.put(each.id(), each));
        for (Answered each : answered.values()) {
            if (!(each.how() instanceof Disposition.Measured(AxisId at))) {
                continue;
            }
            Axis axis = there.get(at);
            if (axis == null) {
                throw new IllegalStateException(
                        "this stage says it measured evidence at an axis it did not keep: "
                                + each.what().id());
            }
            if (!carries(axis, each.what())) {
                throw new IllegalStateException(
                        "this stage says it measured " + each.what().id() + " at " + at
                                + ", which carries nothing that rule drew");
            }
        }
        everyPieceWasDisposedOf();
    }

    /** Whether {@code axis} carries what {@code evidence} draws, asked in that evidence's own
     *  terms. */
    private static boolean carries(Axis axis, LineEvidence evidence) {
        OriginRef by = evidence.by();
        return switch (evidence) {
            // A line the position has no value beside is not a cut of it. It parts the values all
            // the same, and where it parts them is what carries the rule — as the authored line,
            // which is the key that side keeps.
            case LineEvidence.Divides(Threshold line) when line.value() == null ->
                    axis.parted().stream()
                            .anyMatch(each -> each.alternatives().contains(by.authoredLine()));
            // And one it has a value beside is a cut, as is a value singled out: a rule that
            // singles nothing out is not one of those, so there is always a value here.
            case LineEvidence.Divides _, LineEvidence.Singles _ ->
                    axis.cuts().stream().anyMatch(each -> each.origins().contains(by));
        };
    }

    /** That this stage said what became of everything it was handed. */
    private void everyPieceWasDisposedOf() {
        List<LineEvidence.FiledEvidenceId> lost = owed.keySet().stream()
                .filter(each -> !answered.containsKey(each)).toList();
        if (!lost.isEmpty()) {
            throw new IllegalStateException(
                    "the rules said something this stage did not say what became of: " + lost
                            + " — a measure reported as complete over evidence that went missing"
                            + " is what this account exists to refuse");
        }
        List<LineEvidence.FiledEvidenceId> strangers = answered.keySet().stream()
                .filter(each -> !owed.containsKey(each)).toList();
        if (!strangers.isEmpty()) {
            throw new IllegalStateException(
                    "this stage said what became of evidence it was not handed: " + strangers);
        }
    }
}
