package souther.compiler.partition;

import souther.compiler.collect.LatelyAsked;
import souther.compiler.inputs.SearchRegion;

import java.util.function.Supplier;

/**
 * What a run's answers narrowed each region by in one reading of a body
 * ({@link Reachability.Reaching#narrowedPast}), each handed back to whoever asks of the same region
 * and the same answers again while the reading lasts.
 *
 * <p>A way and the ways it is split into share one region wherever what the ways ask apart is
 * nothing a region says — truths, cases — and every one of them is taken past what the run to the
 * border got past working out. The narrowing is of the region and the answers alone, so it is the
 * same for all of them.
 *
 * <p><b>The same region and the same answers, and not equal ones.</b> Asked by identity, so that
 * telling one region from another costs nothing beside the narrowing it saves; a region equal to
 * one asked before but another value is narrowed for itself, to the same answer.
 *
 * <p>Held by the reading and by nothing it answers, as {@link WaysWalked} is, and let go when the
 * reading ends. Outside a reading every region is narrowed when it is asked.
 */
final class RegionsGotPast {

    /** How many regions a reading keeps the narrowing of: more than one body's ways come to. */
    private static final int REGIONS_KEPT = 256;

    private static final ScopedValue<RegionsGotPast> READING = ScopedValue.newInstance();

    private final LatelyAsked<Asked, Reachability.Reaching.NarrowedPast> narrowed =
            new LatelyAsked<>(REGIONS_KEPT);

    private RegionsGotPast() {
    }

    /** What {@code reading} comes to, every region it narrows by the same answers narrowed
     *  once. */
    static <T> T over(Supplier<T> reading) {
        return ScopedValue.where(READING, new RegionsGotPast()).call(reading::get);
    }

    /** What {@code answered} narrows {@code region} by: as this reading narrowed it already, or
     *  {@code narrowing}'s, now. */
    static Reachability.Reaching.NarrowedPast of(
            SearchRegion region, DemandReading.Answered answered,
            Supplier<Reachability.Reaching.NarrowedPast> narrowing) {
        if (!READING.isBound()) {
            return narrowing.get();
        }
        return READING.get().narrowed.answer(new Asked(region, answered), _ -> narrowing.get());
    }

    /** A region and the answers it is narrowed by, each by identity. */
    private static final class Asked {

        private final SearchRegion region;
        private final DemandReading.Answered answered;

        Asked(SearchRegion region, DemandReading.Answered answered) {
            this.region = region;
            this.answered = answered;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof Asked that && region == that.region
                    && answered == that.answered;
        }

        @Override
        public int hashCode() {
            return 31 * System.identityHashCode(region) + System.identityHashCode(answered);
        }
    }
}
