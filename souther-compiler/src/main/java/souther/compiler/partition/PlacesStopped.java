package souther.compiler.partition;

import souther.compiler.inputs.BlockReason;
import souther.compiler.inputs.FilingCoordinate;
import souther.compiler.inputs.RuleSite;

import java.util.Collections;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Objects;
import java.util.SequencedMap;
import java.util.SequencedSet;

/**
 * Where a reading stopped: each place it left the rule at, what stopped the reading there, and the
 * expressions its author wrote that it stopped at.
 *
 * <p>One value for the three, because they are one fact about a place. Held as a map of reasons
 * beside a set of expressions, the two agree only while a single stop made them, and the first
 * time several readings of one comparison are put together a place is sent to an expression that
 * stopped a different place. Here the only way to put two together is {@link #and}, which says
 * what is kept of each.
 *
 * @param at the places, in the order they were met
 */
record PlacesStopped(SequencedMap<FilingCoordinate, Stop> at) {

    /** Nothing stopped anywhere. */
    static final PlacesStopped NOWHERE = new PlacesStopped(new LinkedHashMap<>());

    /**
     * What stopped the reading at one place.
     *
     * @param reason what stopped it, in this compiler's own terms
     * @param sentTo the expressions the author wrote that the arithmetic stopped at on the way to
     *               leaving the rule here; empty where the reading stopped at none of them
     */
    record Stop(BlockReason.RuleReadingStopped reason, SequencedSet<RuleSite> sentTo) {

        Stop {
            Objects.requireNonNull(reason, "a place is left for a reason");
            sentTo = RuleSite.held(sentTo);
        }
    }

    PlacesStopped {
        at = Collections.unmodifiableSequencedMap(new LinkedHashMap<>(at));
    }

    /** These places and their reasons, stopped at no expression an author wrote. */
    static PlacesStopped of(SequencedMap<FilingCoordinate, BlockReason.RuleReadingStopped> reasons) {
        return of(reasons, RuleSite.NO_SITES);
    }

    /** These places and their reasons, all left by the one stop at {@code sentTo}. */
    static PlacesStopped of(SequencedMap<FilingCoordinate, BlockReason.RuleReadingStopped> reasons,
                            SequencedSet<RuleSite> sentTo) {
        SequencedMap<FilingCoordinate, Stop> out = new LinkedHashMap<>();
        reasons.forEach((place, reason) -> out.put(place, new Stop(reason, sentTo)));
        return new PlacesStopped(out);
    }

    boolean isEmpty() {
        return at.isEmpty();
    }

    /** What stopped the reading at each place, without the expressions. */
    SequencedMap<FilingCoordinate, BlockReason.RuleReadingStopped> reasons() {
        SequencedMap<FilingCoordinate, BlockReason.RuleReadingStopped> out = new LinkedHashMap<>();
        at.forEach((place, stop) -> out.put(place, stop.reason()));
        return out;
    }

    /** The expressions the reading stopped at to leave the rule at {@code place}. */
    SequencedSet<RuleSite> sentTo(FilingCoordinate place) {
        Stop stop = at.get(place);
        return stop == null ? RuleSite.NO_SITES : stop.sentTo();
    }

    /**
     * Two readings of one comparison put together: a place keeps the reason of the one that met it
     * first, and every expression either stopped at to leave it there.
     *
     * <p>The expressions of a place only, and never of a place beside it. Two applications of one
     * closure that stop at different calls at different places leave each place with its own call.
     */
    PlacesStopped and(PlacesStopped other) {
        if (other.isEmpty()) {
            return this;
        }
        if (isEmpty()) {
            return other;
        }
        SequencedMap<FilingCoordinate, Stop> out = new LinkedHashMap<>(at);
        other.at.forEach((place, stop) -> out.merge(place, stop, (kept, also) -> {
            SequencedSet<RuleSite> both = new LinkedHashSet<>(kept.sentTo());
            both.addAll(also.sentTo());
            return new Stop(kept.reason(), both);
        }));
        return new PlacesStopped(out);
    }

    /**
     * These places beside the ones already here, where the values a side holds came from.
     *
     * <p>A place that was not stopped at by any reading has no stop of its own to be sent to. The
     * comparison it is filed for was read and stopped, so it is sent to every expression this
     * reading stopped at, which is the whole of what is known about why the comparison was not
     * read.
     */
    PlacesStopped alsoFiledAt(Map<FilingCoordinate, BlockReason.RuleReadingStopped> more) {
        SequencedSet<RuleSite> every = new LinkedHashSet<>();
        at.values().forEach(stop -> every.addAll(stop.sentTo()));
        SequencedMap<FilingCoordinate, Stop> out = new LinkedHashMap<>(at);
        more.forEach((place, reason) -> out.putIfAbsent(place, new Stop(reason, every)));
        return new PlacesStopped(out);
    }
}
