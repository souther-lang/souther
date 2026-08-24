package souther.compiler.reading;

import java.util.List;

/**
 * What the walk carries down: how the place it is at is reached, and what it can say about that.
 *
 * <p>{@link PathAccess} with one more case, and the extra case is the whole reason this is not that.
 * Where the ways in cannot be enumerated or run past the bound, the reading falls back on naming the
 * arm itself — which is a way in that holds a run to something and steers no row anywhere. A walk
 * looking for meetings goes on under it, so the fallback is carried; a reader asking how to compose
 * a row that arrives here is told what is missing instead, which is what {@link #told()} answers.
 * One value with both, so that the fallback cannot reach a caller that would compose from it.
 */
sealed interface Reach {

    /** The ways here, all of them named. Never empty. */
    record Ways(List<WayIn> ways) implements Reach {

        public Ways {
            ways = List.copyOf(ways);
            if (ways.isEmpty()) {
                throw new IllegalArgumentException("a place reached no way is Nothing");
            }
        }

        @Override
        public PathAccess told(souther.compiler.coverage.ControlClaim arrivesAt) {
            return new PathAccess.Ways(ways, arrivesAt);
        }
    }

    /**
     * Ways that hold a run to something and steer no row: a fork this reading could not value,
     * standing on the way here.
     *
     * @param why what left the reading with these rather than the ways themselves
     */
    record Coarse(List<WayIn> ways, PathAccess.Unsupported.Why why) implements Reach {

        public Coarse {
            ways = List.copyOf(ways);
            if (ways.isEmpty()) {
                throw new IllegalArgumentException("a place reached no way is Nothing");
            }
        }

        @Override
        public PathAccess told(souther.compiler.coverage.ControlClaim arrivesAt) {
            return new PathAccess.Unsupported(why);
        }
    }

    /** No run gets here. */
    record Nothing(PathAccess.Unreachable.Why why) implements Reach {

        @Override
        public List<WayIn> ways() {
            return List.of();
        }

        @Override
        public PathAccess told(souther.compiler.coverage.ControlClaim arrivesAt) {
            return new PathAccess.Unreachable(why);
        }
    }

    /** Nothing here can be said in the terms a way in is written in. */
    record Unnameable(PathAccess.Unsupported.Why why) implements Reach {

        @Override
        public List<WayIn> ways() {
            return List.of();
        }

        @Override
        public PathAccess told(souther.compiler.coverage.ControlClaim arrivesAt) {
            return new PathAccess.Unsupported(why);
        }
    }

    /** The ways to go on under, which the last two have none of. */
    List<WayIn> ways();

    /**
     * What a place reached this way is told, which is never the coarse ways themselves.
     *
     * <p>The place's own claim is asked for whatever this came to, because only the reading that
     * knows where it is has one — the walk carries how to get somewhere and never what somewhere
     * is. Where there are ways, it is half of the answer: what steers a row here and what a run
     * that arrived is seen doing are two facts and a search for a row through here needs both.
     */
    PathAccess told(souther.compiler.coverage.ControlClaim arrivesAt);
}
