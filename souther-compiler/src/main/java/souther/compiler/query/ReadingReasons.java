package souther.compiler.query;

import souther.compiler.observe.Incompleteness;
import souther.compiler.partition.ReadingGap;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/**
 * Why the readings of one point could not settle it, as the reasons a reader is told.
 *
 * <p>Not what the readings went without. That is a {@link WeakeningSet}, it is keyed on the border
 * each reading was made at, and it is right to be: a module's account of what its measurement went
 * without counts one fact per line that could not be read. This is the other question about the
 * same readings — what an author is told about this one point — and the border is no part of its
 * answer, because the readings are named under the point, one to a line, and a clause repeated once
 * per reading identifies nothing.
 *
 * <p>So the same reason met at seven readings is one reason here, and two readings stopped in two
 * ways are two. What the count of readings that met a reason would say is how many paths a fact
 * arrived by, which is a fact about the walk.
 *
 * <p><b>The order is a sequence and not a rank.</b> A report is read against the last run, so which
 * reason is said first cannot come from the order a walk happened to take. What that takes is a
 * total order over the reasons, and a total order over a finite set is the set written out in
 * order — {@link #everyReason()}. Written instead as a number per reason, the carrier is wider than
 * the thing: two reasons can be given one number, a sort is stable, and the two then come out in
 * the order they were found in. Here there is no number to get wrong.
 *
 * <p>The order carries no meaning of its own — no reason outranks another — and it is written here
 * rather than taken from how the reasons or the observation codes are declared, so that arranging
 * either of those declarations is not a change to what a report says.
 *
 * <p><b>Checked and never repaired.</b> The projection from what the readings went without to what
 * they are told about is one boundary ({@link ObligationDisposition#of}), and a constructor that
 * quietly put whatever it was handed in order would spread that boundary to everywhere one of these
 * is made. So a list that repeats a reason, is out of order, or holds a reason with no place in the
 * order is refused rather than mended.
 *
 * <p><b>Empty is an answer.</b> A point can be left undecided by something that is not a reading of
 * its own — a row that never ran, which bears on every line and is said where the row stopped — and
 * then there is no reason of the readings' to say here. That is not the absence of an answer: the
 * projection is a {@code switch} over every way a measurement is weakened, so an empty list is
 * every one of them having been classified as said elsewhere.
 *
 * @param eachKindOnce the reasons, one per distinct reason, in the order of {@link #everyReason()}
 */
public record ReadingReasons(List<ReadingGap> eachKindOnce) {

    /**
     * Every reason a reading can meet, in the order a report says them in.
     *
     * <p>The one place the order is decided, and the reason nothing else has to be kept in step
     * with it. That this holds every reason there is, is not something a sequence can say for
     * itself — it is the one property here a check has to carry, and the check reads the reasons
     * off {@link ReadingGap} and {@link Incompleteness.Code} rather than off a second list.
     */
    private static final List<ReadingGap> EVERY_REASON = List.of(
            ReadingGap.of(Incompleteness.Code.VALUE_UNREADABLE),
            ReadingGap.of(Incompleteness.Code.VALUE_TRUNCATED),
            ReadingGap.of(Incompleteness.Code.ROW_UNDECIDED),
            ReadingGap.of(Incompleteness.Code.ANSWERER_NOT_ESTABLISHED),
            ReadingGap.of(Incompleteness.Code.LINKAGE_FAILED),
            ReadingGap.of(Incompleteness.Code.OBSERVATION_ABSENT),
            ReadingGap.of(Incompleteness.Code.INSTRUMENTATION_ABSENT),
            ReadingGap.NO_VALUE);

    public ReadingReasons {
        if (eachKindOnce == null) {
            throw new IllegalArgumentException(
                    "a point nothing could settle says what its readings met");
        }
        eachKindOnce = List.copyOf(eachKindOnce);
        int last = -1;
        for (ReadingGap each : eachKindOnce) {
            int here = EVERY_REASON.indexOf(each);
            if (here < 0) {
                throw new IllegalArgumentException(
                        "a reason with no place in the order a report says them in: " + each);
            }
            // One condition for three ways of being wrong. A repeat, a pair out of order and two
            // reasons in one place are all a position that did not move forward.
            if (here <= last) {
                throw new IllegalArgumentException("the reasons the readings met are said once"
                        + " each, in the order a report says them in: " + eachKindOnce);
            }
            last = here;
        }
    }

    /**
     * The reasons met by a collection of readings, each once and in order.
     *
     * <p>Reachable only from the fold that makes the projection ({@link ObligationDisposition#of}).
     * Offered wider, it would be a second way to arrive at one of these — one that puts in order
     * whatever it is handed — and the boundary the constructor is checking would be wherever
     * somebody called this.
     *
     * <p>Built by taking the order and keeping what was met, rather than by taking what was met and
     * putting it in order. Nothing here compares two reasons, so there is no comparison to be
     * undecided between two of them.
     */
    static ReadingReasons of(Iterable<ReadingGap> met) {
        Set<ReadingGap> found = new LinkedHashSet<>();
        for (ReadingGap each : met) {
            found.add(each);
        }
        List<ReadingGap> out = EVERY_REASON.stream().filter(found::contains).toList();
        if (out.size() != found.size()) {
            // A reason the readings met that the order does not hold. Said rather than dropped: a
            // point would otherwise be undecided for a reason nothing anywhere reports.
            throw new IllegalArgumentException("the readings met a reason with no place in the"
                    + " order a report says them in: " + found);
        }
        return new ReadingReasons(out);
    }

    /** The order itself, for the check that it holds every reason there is. */
    static List<ReadingGap> everyReason() {
        return EVERY_REASON;
    }
}
