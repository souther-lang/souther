package souther.compiler.query;

import souther.compiler.partition.ReadingGap;
import souther.compiler.publish.CanonicalSelection;
import souther.compiler.publish.PublicationOrders;

import java.util.Collection;
import java.util.Objects;

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
 * <p><b>A meaning and not a mechanism.</b> That the reasons are said each once and in one order is
 * {@link CanonicalSelection}'s, and the order itself is
 * {@link PublicationOrders#READING_GAPS}. What this name adds is which question the reasons answer,
 * which the sequence cannot say for itself and which is the whole of the difference between these
 * and the set of facts a measurement went without.
 *
 * <p><b>Empty is an answer.</b> A point can be left undecided by something that is not a reading of
 * its own — a row that never ran, which bears on every line and is said where the row stopped — and
 * then there is no reason of the readings' to say here. That is not the absence of an answer: the
 * projection is a {@code switch} over every way a measurement is weakened, so an empty selection is
 * every one of them having been classified as said elsewhere.
 *
 * @param eachKindOnce the reasons, one per distinct reason, in the order they are published in
 */
public record ReadingReasons(CanonicalSelection<ReadingGap> eachKindOnce) {

    public ReadingReasons {
        Objects.requireNonNull(eachKindOnce,
                "a point nothing could settle says what its readings met");
    }

    /**
     * The reasons a collection of readings met, each once and in order.
     *
     * <p>Offered to anybody, because there is nothing here for a caller to get wrong: what comes
     * out is the written order with what was met kept, and a second caller reaches the same value
     * as the first. No caller puts anything in order, so there is no second place for the order to
     * be decided in.
     */
    public static ReadingReasons of(Collection<ReadingGap> met) {
        return new ReadingReasons(PublicationOrders.READING_GAPS.keep(met));
    }
}
