package souther.compiler.query;

import souther.compiler.observe.MeasureReason;
import souther.compiler.publish.CanonicalSelection;
import souther.compiler.publish.PublicationOrders;

import java.util.ArrayList;
import java.util.Collection;
import java.util.List;

/**
 * Why one authored line is unmeasured, over the readings of it that account for that.
 *
 * <p>What {@link WeakeningSet} is to a reading that stopped short, one grain up: a debt is read at
 * every position of every behavior carrying the type, and where several of those readings are why
 * nothing was read against the point, what the debt says is all of them. Held as one reason, what a
 * debt said was whichever reading came later in the walk, and which reading comes later is the
 * order the lines were gathered in.
 *
 * <p>The readings that account for it, and not every reading that said something. Which readings
 * those are is {@link ObligationCoverage#acrossTheReadings}'s answer and no part of this: a
 * reading with nothing to look at leaves a point where it found it, and one that is here is one
 * this holds.
 *
 * <p><b>The cardinality comes from what the reasons are facts about.</b> A reason about the run is
 * an input to the whole run, so every reading of every line that reaches it says the same one and
 * two different ones at one line is a state no run is in — refused here, where the value is made,
 * rather than by whoever folds. A reason about the behavior is something one behavior says and the
 * next need not, so there is no limit on those.
 *
 * <p>Nothing else is refused. That a reason about the run never arrives beside one about the
 * behavior is true of the readings this compiler makes today, and it is true because of the order
 * the gates in {@code Coverages} are asked in — a fact about a producer, which is not this type's
 * to state.
 *
 * <p>Held in the order they are published in ({@link PublicationOrders#UNASKED_REASONS}), which is
 * a decision about what a reader is shown and no ranking of the reasons. Which of them outranks a
 * miss is asked of what each is — {@link #mayHideARow()} — and never of where it sits here.
 *
 * <p>A value, because these travel inside {@code Db} answers, which is what {@link WeakeningSet}
 * says of itself for the same reason.
 */
public final class UnaskedReasons {

    /** The reasons, each once, in the order a document says them and never in the order the
     *  readings were walked in. */
    private final CanonicalSelection<ItemAssessment.Coverage.NotAsked> reasons;

    private UnaskedReasons(CanonicalSelection<ItemAssessment.Coverage.NotAsked> reasons) {
        this.reasons = reasons;
    }

    /** What one reading gave. */
    public static UnaskedReasons of(ItemAssessment.Coverage.NotAsked one) {
        return ofAll(List.of(one));
    }

    public static UnaskedReasons ofAll(Collection<ItemAssessment.Coverage.NotAsked> given) {
        if (given.isEmpty()) {
            throw new IllegalArgumentException(
                    "a point nobody read against says why nobody did, and this says nothing");
        }
        CanonicalSelection<ItemAssessment.Coverage.NotAsked> held =
                PublicationOrders.UNASKED_REASONS.keep(given);
        List<ItemAssessment.Coverage.NotAsked> ofTheRun = new ArrayList<>();
        for (ItemAssessment.Coverage.NotAsked each : held.written()) {
            if (each.about() == MeasureReason.About.THE_RUN) {
                ofTheRun.add(each);
            }
        }
        if (ofTheRun.size() > 1) {
            throw new IllegalArgumentException("one line, and two things the run asked for: "
                    + ofTheRun);
        }
        return new UnaskedReasons(held);
    }

    /** The reasons, each once, in the order a document says them. */
    public CanonicalSelection<ItemAssessment.Coverage.NotAsked> reasons() {
        return reasons;
    }

    /**
     * Whether a row at the point could be sitting behind any of these and not have been seen.
     *
     * <p>Any of them, because each is a reason nothing was read and one that could be hiding a row
     * is enough to leave the point unanswered. Not read off what the reasons are facts about: the
     * two questions agree over these three constants and part elsewhere, and a reader that derived
     * one from the other would be right by coincidence.
     */
    public boolean mayHideARow() {
        for (ItemAssessment.Coverage.NotAsked each : reasons.written()) {
            if (each.mayHideARow()) {
                return true;
            }
        }
        return false;
    }

    /**
     * The one reason, for somewhere that has room for one.
     *
     * <p>A boundary item of the report says a single {@code reason}, the opening under a verdict
     * names one, the sentence beside a point reads as one, and a reading's own
     * {@link Measurement.NotMeasured} holds the one reason that reading asked nothing for. So the
     * projection is written here rather than left to each of them taking whichever came first — an
     * account holding more than one reason is not something any of them can say, and this says so
     * instead of choosing.
     *
     * <p><b>The refusal is the contract and not a reading of what reaches it.</b> Nothing here
     * rests on the readings this compiler makes today coming to one. The day one comes to two, this
     * is where it is said that there is no room for the second, and what to do about that is
     * decided then rather than lost.
     */
    public ItemAssessment.Coverage.NotAsked asOne() {
        if (reasons.size() != 1) {
            throw new IllegalStateException("a surface that says one reason cannot say " + reasons);
        }
        return reasons.written().get(0);
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof UnaskedReasons it && reasons.equals(it.reasons);
    }

    @Override
    public int hashCode() {
        return reasons.hashCode();
    }

    @Override
    public String toString() {
        return reasons.toString();
    }
}
