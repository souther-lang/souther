package souther.compiler.query;

import souther.compiler.observe.Incompleteness;
import souther.compiler.partition.ReadingGap;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;

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
 * <p><b>Ordered, and the order is written here.</b> The report is read by a person comparing one
 * run with the last, so which reason is said first cannot come from the order a walk happened to
 * take. The order carries no meaning of its own — no reason outranks another — and it is fixed here
 * rather than taken from how the reasons or the observation codes are declared, so that arranging
 * either of those declarations is not a change to what a report says.
 *
 * <p><b>Checked and never repaired.</b> The projection from what the readings went without to what
 * they are told about is one boundary ({@link ObligationDisposition#of}), and a constructor that
 * quietly sorted and deduplicated whatever it was handed would spread that boundary to everywhere
 * one of these is made. So a list that repeats a reason or is out of order is refused.
 *
 * <p><b>Empty is an answer.</b> A point can be left undecided by something that is not a reading of
 * its own — a row that never ran, which bears on every line and is said where the row stopped — and
 * then there is no reason of the readings' to say here. That is not the absence of an answer: the
 * projection is a {@code switch} over every way a measurement is weakened, so an empty list is
 * every one of them having been classified as said elsewhere.
 *
 * @param eachKindOnce the reasons, one per distinct reason, in the order below
 */
public record ReadingReasons(List<ReadingGap> eachKindOnce) {

    public ReadingReasons {
        if (eachKindOnce == null) {
            throw new IllegalArgumentException(
                    "a point nothing could settle says what its readings met");
        }
        eachKindOnce = List.copyOf(eachKindOnce);
        for (int i = 1; i < eachKindOnce.size(); i++) {
            ReadingGap before = eachKindOnce.get(i - 1);
            ReadingGap here = eachKindOnce.get(i);
            if (before.equals(here)) {
                throw new IllegalArgumentException(
                        "a reason the readings met is said once: " + here);
            }
            if (orderOf(before) > orderOf(here)) {
                throw new IllegalArgumentException(
                        "the reasons the readings met are said in order: " + eachKindOnce);
            }
        }
    }

    /**
     * The reasons met by a collection of readings, each once and in order.
     *
     * <p>Reachable only from the fold that makes the projection ({@link ObligationDisposition#of}).
     * Offered wider, it would be a second way to arrive at one of these — one that repairs whatever
     * it is handed — and the boundary the constructor is checking would be wherever somebody called
     * this.
     */
    static ReadingReasons of(Iterable<ReadingGap> met) {
        List<ReadingGap> out = new ArrayList<>();
        for (ReadingGap each : met) {
            if (!out.contains(each)) {
                out.add(each);
            }
        }
        out.sort(Comparator.comparingInt(ReadingReasons::orderOf));
        return new ReadingReasons(out);
    }

    /**
     * Where one reason sits in the order a report says them in.
     *
     * <p>Exhaustive, so a reason added is a compile error here rather than one that sorts equal to
     * something else and comes out wherever a walk put it. What the numbers are says nothing; that
     * they are written down is the whole of it.
     */
    private static int orderOf(ReadingGap gap) {
        return switch (gap) {
            case ReadingGap.Observation(Incompleteness.Code code) -> orderOf(code);
            case ReadingGap.NoValue _ -> 100;
        };
    }

    /** The same for the code an observation that stopped carries. */
    private static int orderOf(Incompleteness.Code code) {
        return switch (code) {
            case VALUE_UNREADABLE -> 0;
            case VALUE_TRUNCATED -> 1;
            case ROW_UNDECIDED -> 2;
            case ANSWERER_NOT_ESTABLISHED -> 3;
            case LINKAGE_FAILED -> 4;
            case OBSERVATION_ABSENT -> 5;
            case INSTRUMENTATION_ABSENT -> 6;
        };
    }
}
