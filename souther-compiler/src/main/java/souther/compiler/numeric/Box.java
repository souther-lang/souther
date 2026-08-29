package souther.compiler.numeric;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;

/**
 * What each position is known to lie between, exactly, at one moment.
 *
 * <p>A value and not a view. What reads this is handed the whole of it and cannot ask anything else
 * — not the constraints it came from, not what has been derived since, not what another position
 * was narrowed to in the same round. That is what makes a reduction over it a function of what it
 * was given rather than of the order the reductions happened to run in: every rule reads the same
 * box, and what they all found is put together afterwards.
 *
 * <p>A missing end is no bound that way, not a bound at nothing. A position this says nothing about
 * runs the whole way in both directions.
 */
public record Box<A>(Map<A, RationalCut> atLeast, Map<A, RationalCut> atMost) {

    public Box {
        atLeast = Map.copyOf(atLeast);
        atMost = Map.copyOf(atMost);
    }

    public static <A> Box<A> unbounded() {
        return new Box<>(Map.of(), Map.of());
    }

    /** The tightest {@code atom >= …} this holds, or {@code null} for no bound below. */
    public RationalCut leastOf(A atom) {
        return atLeast.get(atom);
    }

    /** The tightest {@code atom <= …} this holds, or {@code null} for no bound above. */
    public RationalCut mostOf(A atom) {
        return atMost.get(atom);
    }

    /** Every position this says anything about. */
    public Set<A> positions() {
        Set<A> out = new LinkedHashSet<>(atLeast.keySet());
        out.addAll(atMost.keySet());
        return out;
    }

    /**
     * This box narrowed by {@code found}, each end kept at whichever of the two is tighter.
     *
     * <p>Both directions at once, because a reduction hands back what it found on either side and
     * the two are one answer about the position.
     */
    public Box<A> meeting(Map<A, RationalCut> foundAtLeast, Map<A, RationalCut> foundAtMost) {
        Map<A, RationalCut> least = new LinkedHashMap<>(atLeast);
        foundAtLeast.forEach((atom, cut) -> least.merge(atom, cut, RationalCut::tighterLower));
        Map<A, RationalCut> most = new LinkedHashMap<>(atMost);
        foundAtMost.forEach((atom, cut) -> most.merge(atom, cut, RationalCut::tighterUpper));
        return new Box<>(least, most);
    }

    /**
     * Whether some value lies between the two ends at {@code atom}.
     *
     * <p>Asked of the ends and not of their values. At one value the two ends are the same place and
     * what decides it is whether both admit it — over values that fill there is nothing else between
     * them to fall back on.
     */
    public boolean holdsAValueAt(A atom) {
        RationalCut low = atLeast.get(atom);
        RationalCut high = atMost.get(atom);
        if (low == null || high == null) {
            return true;
        }
        int order = low.at().compareTo(high.at());
        if (order > 0) {
            return false;
        }
        return order < 0 || (low.inclusive() && high.inclusive());
    }

    /** Whether every position this speaks of is left a value. */
    public boolean holdsAValue() {
        return positions().stream().allMatch(this::holdsAValueAt);
    }
}
