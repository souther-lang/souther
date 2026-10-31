package souther.compiler.partition;

import souther.compiler.collect.LatelyAsked;

import java.util.List;
import java.util.function.Supplier;

/**
 * The walks of ways one reading of a body has walked ({@link WayToTheBorder#along}), each handed
 * back to whoever asks for the same way again while the reading lasts.
 *
 * <p>A walk is of the conditions on the way and nothing else: what it takes in is read by one
 * vocabulary and stopped by figures that are constants, and what the declarations leave does not
 * enter it. A reading reads one way over many regions and for many relations, each building the
 * way afresh from the same conditions, so the walks it asks for are a few walked many times.
 *
 * <p><b>The same conditions, and not equal ones.</b> A way is the conditions on it in their order,
 * each by identity: what a walk hands back names the choices it made by the entry they were made
 * at, and its readers look them up by identity. A walk of conditions equal to these but not these
 * would name entries the asker does not hold.
 *
 * <p><b>Held by the reading and by nothing it answers.</b> What comes back is the walk itself, the
 * figure that stopped it and the order of its ways included, so an asker cannot tell a walk handed
 * back from one walked for it, and what it builds from the walk is what it built before. When the
 * reading ends this is let go. Any figure an asker counts its walks by is its own, and an asker
 * counting the ways it asks to have walked counts one handed back as one walked.
 */
final class WaysWalked {

    /** How many ways a reading keeps the walks of: more than one body's conditions come to. */
    private static final int WAYS_KEPT = 256;

    private static final ScopedValue<WaysWalked> READING = ScopedValue.newInstance();

    private final LatelyAsked<Conditions, OneOfEach.Walked<OnTheWay, Reachability>> walked =
            new LatelyAsked<>(WAYS_KEPT);

    /** How many of the walks asked for were walked rather than handed back. */
    private int walks;

    private WaysWalked() {
    }

    /** What {@code reading} comes to, every way it asks to have walked walked once. */
    static <T> T over(Supplier<T> reading) {
        return ScopedValue.where(READING, new WaysWalked()).call(reading::get);
    }

    /** The walk of {@code onTheWay}: the one this reading walked already, or {@code walking}'s,
     *  walked now. Outside a reading, walked every time it is asked. */
    static OneOfEach.Walked<OnTheWay, Reachability> along(
            List<OnTheWay> onTheWay, Supplier<OneOfEach.Walked<OnTheWay, Reachability>> walking) {
        if (!READING.isBound()) {
            return walking.get();
        }
        WaysWalked reading = READING.get();
        return reading.walked.answer(new Conditions(onTheWay), _ -> {
            reading.walks++;
            return walking.get();
        });
    }

    /** How many walks the reading this runs in walked rather than handed back; none outside
     *  one. */
    static int walkedSoFar() {
        return READING.isBound() ? READING.get().walks : 0;
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
}
