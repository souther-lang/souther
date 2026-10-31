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
 * Where a reading stopped: each stop it made, which left a rule at one place, for one reason, at
 * one expression its author wrote or at none.
 *
 * <p>The stops are held whole and are never combined. A place, a reason and a call are one fact,
 * and the three are not independent: a call belongs to the reason it stopped for, at the place it
 * stopped. Combined by component — a reason kept, the calls of both readings gathered under it —
 * a call arrived at a place or a reason it did not belong to, and it did so in each way a
 * combination can be written. So putting readings together ({@link #and}) only gathers their
 * stops, and everything a reader asks is selected from them by the one policy below.
 *
 * <p><b>The policy.</b> A place is left with the reason of the first stop that met it, as a map
 * keeps the first of what is put at a key. It is sent to the calls of every stop at it for that
 * same reason ({@link BlockReason#factOf}, which leaves out the figures a reason was met at), and
 * to none of the calls that stopped it for another. A stop at no call an author wrote sends a
 * reader to the rule, and adds nothing to the calls.
 *
 * @param stops the stops, each once, in the order they were met
 */
record PlacesStopped(SequencedSet<Stop> stops) {

    /** Nothing stopped anywhere. */
    static final PlacesStopped NOWHERE = new PlacesStopped(new LinkedHashSet<>());

    /**
     * One stop: a place the rule was left at, what stopped the reading there, and where a reader
     * goes about it.
     *
     * @param sentTo the expression its author wrote that the arithmetic stopped at, or
     *               {@link RuleSite#theRuleItself()} where it stopped at none
     */
    record Stop(FilingCoordinate place, BlockReason.RuleReadingStopped reason, RuleSite sentTo) {

        Stop {
            Objects.requireNonNull(place, "a rule is left somewhere");
            Objects.requireNonNull(reason, "a place is left for a reason");
            Objects.requireNonNull(sentTo, "a stop is sent somewhere");
        }
    }

    PlacesStopped {
        stops = Collections.unmodifiableSequencedSet(new LinkedHashSet<>(stops));
    }

    /** These places and their reasons, stopped at no expression an author wrote. */
    static PlacesStopped of(SequencedMap<FilingCoordinate, BlockReason.RuleReadingStopped> reasons) {
        return of(reasons, RuleSite.NO_SITES);
    }

    /**
     * These places and their reasons, all left by the one stop at {@code sentTo} — at none where
     * that is empty.
     */
    static PlacesStopped of(SequencedMap<FilingCoordinate, BlockReason.RuleReadingStopped> reasons,
                            SequencedSet<RuleSite> sentTo) {
        SequencedSet<Stop> out = new LinkedHashSet<>();
        reasons.forEach((place, reason) -> {
            if (sentTo.isEmpty()) {
                out.add(new Stop(place, reason, RuleSite.theRuleItself()));
            }
            sentTo.forEach(site -> out.add(new Stop(place, reason, site)));
        });
        return new PlacesStopped(out);
    }

    boolean isEmpty() {
        return stops.isEmpty();
    }

    /** Two readings of one comparison put together: the stops of both, in the order met. */
    PlacesStopped and(PlacesStopped other) {
        if (other.isEmpty()) {
            return this;
        }
        if (isEmpty()) {
            return other;
        }
        SequencedSet<Stop> both = new LinkedHashSet<>(stops);
        both.addAll(other.stops);
        return new PlacesStopped(both);
    }

    /** Every place a stop left the rule at, in the order they were met. */
    SequencedSet<FilingCoordinate> places() {
        SequencedSet<FilingCoordinate> out = new LinkedHashSet<>();
        stops.forEach(stop -> out.add(stop.place()));
        return out;
    }

    /**
     * What a place is left with.
     *
     * @param reason the reason of the first stop that met the place
     * @param sentTo the calls an author wrote that the arithmetic stopped at to leave the rule
     *               here for that reason; empty where it stopped at none, and a reader is sent to
     *               the rule
     */
    record Decided(BlockReason.RuleReadingStopped reason, SequencedSet<RuleSite> sentTo) {}

    /**
     * What each place is left with, by the policy above, in one pass over the stops.
     */
    SequencedMap<FilingCoordinate, Decided> decided() {
        SequencedMap<FilingCoordinate, BlockReason.RuleReadingStopped> reasons = reasons();
        Map<FilingCoordinate, Object> words = new LinkedHashMap<>();
        reasons.forEach((place, reason) -> words.put(place, BlockReason.factOf(reason)));
        Map<FilingCoordinate, SequencedSet<RuleSite>> calls = new LinkedHashMap<>();
        for (Stop stop : stops) {
            if (!(stop.sentTo() instanceof RuleSite.TheRuleItself)
                    && words.get(stop.place()).equals(BlockReason.factOf(stop.reason()))) {
                calls.computeIfAbsent(stop.place(), _ -> new LinkedHashSet<>()).add(stop.sentTo());
            }
        }
        SequencedMap<FilingCoordinate, Decided> out = new LinkedHashMap<>();
        reasons.forEach((place, reason) -> out.put(place,
                new Decided(reason, RuleSite.held(calls.getOrDefault(place, RuleSite.NO_SITES)))));
        return out;
    }

    /** What each place is left with: the reason of the first stop that met it. */
    SequencedMap<FilingCoordinate, BlockReason.RuleReadingStopped> reasons() {
        SequencedMap<FilingCoordinate, BlockReason.RuleReadingStopped> out = new LinkedHashMap<>();
        stops.forEach(stop -> out.putIfAbsent(stop.place(), stop.reason()));
        return out;
    }

    /** The calls {@code place} is sent to, as {@link Decided} says; none for a place no stop met. */
    SequencedSet<RuleSite> sentTo(FilingCoordinate place) {
        Decided decided = decided().get(place);
        return decided == null ? RuleSite.NO_SITES : decided.sentTo();
    }

    /**
     * These places beside the ones already here, where the values a side holds came from.
     *
     * <p>A place no reading stopped at has no stop of its own to be sent to, and is left sent to
     * the rule: an expression another place was stopped by says nothing of why this one was filed.
     */
    PlacesStopped alsoFiledAt(Map<FilingCoordinate, BlockReason.RuleReadingStopped> more) {
        SequencedSet<FilingCoordinate> known = places();
        SequencedSet<Stop> out = new LinkedHashSet<>(stops);
        more.forEach((place, reason) -> {
            if (!known.contains(place)) {
                out.add(new Stop(place, reason, RuleSite.theRuleItself()));
            }
        });
        return new PlacesStopped(out);
    }
}
