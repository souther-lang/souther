package souther.compiler.partition;

import souther.compiler.inputs.SearchRegion;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Supplier;

/**
 * What one reading of a body's guards works out once and hands back to whoever asks the same
 * again while the reading lasts: the walk of a way ({@link WayToTheBorder#along}), and what a run's
 * answers narrow a region by ({@link Reachability.Reaching#narrowedPast}).
 *
 * <p>A reading reads one way over many regions and for many relations, each building the way afresh
 * from the same conditions; and it takes the way to each case, and each way that is split into,
 * past what the run to the border got past working out, where ways that differ only in what no
 * region says — truths, cases — share one region. Both are functions of what they are asked alone.
 * A walk is of the conditions on the way: one vocabulary reads them and constants stop it, and the
 * declarations do not enter it. A narrowing is of the region and the answers.
 *
 * <p><b>The same things, and not equal ones.</b> Asked by identity. What a walk hands back names
 * the choices it made by the entry they were made at, and its readers look them up by identity, so
 * a walk of conditions equal to these but not these would name entries the asker does not hold. And
 * telling one region from another by identity costs nothing beside the narrowing it saves; a region
 * equal to one asked before but another value is narrowed for itself, to the same answer.
 *
 * <p><b>Held by the reading and by nothing it answers.</b> What comes back is what was worked out
 * — a walk with the figure that stopped it and the order of its ways — so an asker cannot tell an
 * answer handed back from one worked out for it. Everything is kept while the reading lasts, which
 * is no more than it asked, and let go when it ends. Any figure an asker counts its asking by is its
 * own. Outside a reading everything is worked out when it is asked.
 */
final class OneReading {

    private static final ScopedValue<OneReading> READING = ScopedValue.newInstance();

    private final Map<Conditions, OneOfEach.Walked<OnTheWay, Reachability>> walked =
            new HashMap<>();
    private final Map<RegionPast, Reachability.Reaching.NarrowedPast> narrowed = new HashMap<>();

    private OneReading() {
    }

    /** What {@code reading} comes to, each thing it asks to have worked out worked out once. */
    static <T> T over(Supplier<T> reading) {
        return ScopedValue.where(READING, new OneReading()).call(reading::get);
    }

    /** The walk of {@code onTheWay}: the one this reading walked already, or {@code walking}'s,
     *  walked now. */
    static OneOfEach.Walked<OnTheWay, Reachability> walked(
            List<OnTheWay> onTheWay, Supplier<OneOfEach.Walked<OnTheWay, Reachability>> walking) {
        return READING.isBound()
                ? kept(READING.get().walked, new Conditions(onTheWay), walking)
                : walking.get();
    }

    /** What {@code answered} narrows {@code region} by: as this reading narrowed it already, or
     *  {@code narrowing}'s, now. */
    static Reachability.Reaching.NarrowedPast narrowedPast(
            SearchRegion region, DemandReading.Answered answered,
            Supplier<Reachability.Reaching.NarrowedPast> narrowing) {
        return READING.isBound()
                ? kept(READING.get().narrowed, new RegionPast(region, answered), narrowing)
                : narrowing.get();
    }

    /** The answer kept in {@code in} for {@code asked}, or {@code working}'s, kept from now on.
     *  Looked up and put in apart, so working one out may ask for another. */
    private static <K, V> V kept(Map<K, V> in, K asked, Supplier<V> working) {
        V known = in.get(asked);
        if (known != null) {
            return known;
        }
        V made = working.get();
        in.put(asked, made);
        return made;
    }

    /** The conditions on a way, in their order, each by identity. */
    private static final class Conditions {

        private final List<OnTheWay> entries;
        private final int hash;

        Conditions(List<OnTheWay> entries) {
            this.entries = entries;
            int out = 1;
            for (OnTheWay each : entries) {
                out = 31 * out + System.identityHashCode(each);
            }
            this.hash = out;
        }

        @Override
        public boolean equals(Object other) {
            if (!(other instanceof Conditions that) || hash != that.hash
                    || entries.size() != that.entries.size()) {
                return false;
            }
            for (int at = 0; at < entries.size(); at++) {
                if (entries.get(at) != that.entries.get(at)) {
                    return false;
                }
            }
            return true;
        }

        @Override
        public int hashCode() {
            return hash;
        }
    }

    /** A region and the answers it is narrowed by, each by identity. */
    private static final class RegionPast {

        private final SearchRegion region;
        private final DemandReading.Answered answered;

        RegionPast(SearchRegion region, DemandReading.Answered answered) {
            this.region = region;
            this.answered = answered;
        }

        @Override
        public boolean equals(Object other) {
            return other instanceof RegionPast that && region == that.region
                    && answered == that.answered;
        }

        @Override
        public int hashCode() {
            return 31 * System.identityHashCode(region) + System.identityHashCode(answered);
        }
    }
}
