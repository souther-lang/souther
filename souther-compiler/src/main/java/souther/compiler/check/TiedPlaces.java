package souther.compiler.check;

import java.util.ArrayDeque;
import java.util.Collections;
import java.util.Deque;
import java.util.HashSet;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.ConcurrentHashMap;

/**
 * Which places of one value the parts of its rules tie together.
 *
 * <p>A part ties every place it names to every other, and a place at, under or over one a part
 * names is tied to it as well, since a part naming a place reads what is under it. Places no chain
 * of parts joins take what the rules leave each of them whatever the others take, so a value of the
 * places tied to one stands beside every value of the rest.
 *
 * <p>Made once for the readings of one value, from the parts naming each place
 * ({@code InvariantChecker.PartsNaming}), and asked at every place a projection or a relation is
 * asked of: the places tied to one are worked out the first time they are asked, and are the same
 * set for every place among them.
 */
final class TiedPlaces {

    private final Map<RuleKey, Set<InvariantChecker.PartReading>> named;

    /** The places each reading of a part names. */
    private final Map<InvariantChecker.PartReading, Set<RuleKey>> placesOf;

    private final Map<RuleKey, Set<RuleKey>> tied = new ConcurrentHashMap<>();

    private TiedPlaces(Map<RuleKey, Set<InvariantChecker.PartReading>> named,
                       Map<InvariantChecker.PartReading, Set<RuleKey>> placesOf) {
        this.named = named;
        this.placesOf = placesOf;
    }

    /** The places the parts in {@code named} tie together, where {@code named} is the parts
     *  naming each place, as the readings of one value met them. */
    static TiedPlaces of(Map<RuleKey, Set<InvariantChecker.PartReading>> named) {
        Map<InvariantChecker.PartReading, Set<RuleKey>> placesOf = new LinkedHashMap<>();
        named.forEach((place, reads) -> reads.forEach(read ->
                placesOf.computeIfAbsent(read, _ -> new LinkedHashSet<>()).add(place)));
        placesOf.replaceAll((_, places) -> Collections.unmodifiableSet(places));
        return new TiedPlaces(named, Collections.unmodifiableMap(placesOf));
    }

    /** The places each reading of a part names. */
    Map<InvariantChecker.PartReading, Set<RuleKey>> placesOf() {
        return placesOf;
    }

    /** The places the parts tie {@code place} to, {@code place} among them. */
    Set<RuleKey> tiedTo(RuleKey place) {
        Set<RuleKey> known = tied.get(place);
        if (known != null) {
            return known;
        }
        Set<RuleKey> reached = Collections.unmodifiableSet(reached(place, null, null));
        // From a place a part names, every place reached is one a part names and is tied to the
        // same places, so each of them is answered by this one walk. From a place no part names,
        // the set holds that place, which no other place is tied to.
        if (named.containsKey(place)) {
            reached.forEach(each -> tied.putIfAbsent(each, reached));
        } else {
            tied.putIfAbsent(place, reached);
        }
        return reached;
    }

    /**
     * Whether the parts other than {@code part} tie {@code one} to {@code other}: one of them
     * names a place at, under or over each, or names a place at one of them beside a place another
     * such part ties to the other.
     *
     * <p>A question about the rules with one of their parts left out, which the places tied
     * together with every part in do not answer, so it is walked for itself and stops where it
     * meets {@code other}.
     */
    boolean tiedWithout(PartId<RuleRef.Invariant> part, RuleKey one, RuleKey other) {
        return reached(one, part, other) == null;
    }

    /**
     * The places the parts but {@code without}'s readings tie {@code one} to — or null as soon as
     * one of them is at, under or over {@code stopAt}, where that is not null.
     */
    private Set<RuleKey> reached(RuleKey one, PartId<RuleRef.Invariant> without, RuleKey stopAt) {
        Set<RuleKey> reached = new LinkedHashSet<>(List.of(one));
        Deque<RuleKey> todo = new ArrayDeque<>(reached);
        Set<InvariantChecker.PartReading> crossed = new HashSet<>();
        while (!todo.isEmpty()) {
            RuleKey at = todo.pop();
            if (stopAt != null && near(at, stopAt)) {
                return null;
            }
            for (Map.Entry<RuleKey, Set<InvariantChecker.PartReading>> each : named.entrySet()) {
                if (!near(each.getKey(), at)) {
                    continue;
                }
                for (InvariantChecker.PartReading read : each.getValue()) {
                    if (!read.part().equals(without) && crossed.add(read)) {
                        placesOf.get(read).stream().filter(reached::add).forEach(todo::add);
                    }
                }
            }
        }
        return reached;
    }

    /** Whether one of the two places is at or under the other. */
    private static boolean near(RuleKey one, RuleKey other) {
        return one.isAtOrUnder(other) || other.isAtOrUnder(one);
    }
}
