package souther.compiler.reading;

import java.util.Collections;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.SequencedSet;

/**
 * What the walk carries down: how the place it is at is reached, and what it can say about that.
 *
 * <p>{@link PathAccess} with one more case, and the extra case is the whole reason this is not that.
 * Where the ways in cannot be enumerated or run past the bound, the reading falls back on naming the
 * arm itself — which is a way in that holds a run to something and steers no row anywhere. A walk
 * looking for meetings goes on under it, so the fallback is carried; a reader asking how to compose
 * a row that arrives here is told what is missing instead, which is what {@code told} answers.
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
     * Ways that hold a run to something and steer no row: a fork this reading could not value, or
     * whose ways what a run is seen doing does not tell apart, standing on the way here.
     *
     * @param ways  what the walk goes on under, each decision on which is witnessed by its claim:
     *              the arm itself where the fork stands, which a run is seen taking whichever way
     *              it came
     * @param why   what left the reading with these rather than the ways themselves
     * @param known what a run here is known to have decided, one conjunction per way it may have
     *              come: the ways themselves where the fork's ways were written down and only
     *              could not be told apart, and {@code ways} otherwise. Read for what a run reads
     *              and never for what it is seen doing, since a claim on one of these may be passed
     *              by a run on another
     */
    record Coarse(List<WayIn> ways, PathAccess.Unsupported.Why why, List<WayIn> known)
            implements Reach {

        public Coarse {
            ways = List.copyOf(ways);
            known = List.copyOf(known);
            if (ways.isEmpty() || known.isEmpty()) {
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

    /**
     * Nothing here can be said in the terms a way in is written in.
     *
     * @param whys  every step nothing states on the way here, by what left it so, the one a place
     *              here is told first. Every one and not the first: what {@code known} leaves out
     *              is all of them, and a reader asking whether it leaves out anything but a
     *              function value being called is asking about each
     * @param known what is known to hold here as far as it was named: the decisions the ways above
     *              the step nothing states had settled, and whatever is settled under it since. A
     *              step nothing states is taken to rule out nothing, so these are no ways in — a
     *              row composed along one may not get here — and are what a run here is known to
     *              have decided. One way with nothing in it where nothing is known
     */
    record Unnameable(SequencedSet<PathAccess.Unsupported.Why> whys, List<WayIn> known)
            implements Reach {

        public Unnameable {
            whys = Collections.unmodifiableSequencedSet(new LinkedHashSet<>(whys));
            known = List.copyOf(known);
            if (whys.isEmpty()) {
                throw new IllegalArgumentException("a step nothing states is left so for a reason");
            }
            if (known.isEmpty()) {
                throw new IllegalArgumentException("a place runs reach is known by some way, even"
                        + " one nothing is known on; none is Nothing");
            }
        }

        /** A step nothing states, with nothing known about what holds there. */
        Unnameable(PathAccess.Unsupported.Why why) {
            this(new LinkedHashSet<>(List.of(why)), List.of(new WayIn(List.of())));
        }

        /** What a place here is told is missing: the first step nothing states. */
        PathAccess.Unsupported.Why why() {
            return whys.getFirst();
        }

        @Override
        public List<WayIn> ways() {
            return List.of();
        }

        @Override
        public PathAccess told(souther.compiler.coverage.ControlClaim arrivesAt) {
            return new PathAccess.Unsupported(why());
        }
    }

    /** The ways to go on under, which the last two have none of. */
    List<WayIn> ways();

    /**
     * What a run here is known to have decided, one conjunction per way it may have come.
     *
     * <p>The ways themselves where they are named. Under a step nothing states, what was named above
     * it and since — which steers no row and is still what holds wherever a run is. Nothing where
     * no run comes.
     */
    default List<WayIn> known() {
        return switch (this) {
            case Ways it -> it.ways();
            case Coarse it -> it.known();
            case Unnameable it -> it.known();
            case Nothing _ -> List.of();
        };
    }

    /**
     * Whether some run gets here.
     *
     * <p>Not whether the ways here are named. A place under a way in nothing states is one runs
     * reach and this reading cannot say how; a place nothing reaches is one no run gets to, which
     * is a proof about the body. A reader asking what the body does there asks this, and an empty
     * list of ways answers it for neither.
     */
    default boolean someRunArrives() {
        return switch (this) {
            case Ways _, Coarse _, Unnameable _ -> true;
            case Nothing _ -> false;
        };
    }

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
