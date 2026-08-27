package souther.compiler.query;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * One walk down from an answer, written once for whatever is being walked.
 *
 * <p>What a walk of a store and a walk of the declarations were found to disagree about was never
 * what a thing is — it was the walking: which paths a thing found under something is written out
 * at, what happens when a walk comes back to where it already is, and how much was looked at. Each
 * had its own answer, and every defect either of them had was a rule the other one already kept.
 *
 * <p>So the walking is here and what is being walked is {@link WhatStandsHere.Facts}'s. This keeps:
 *
 * <ul>
 *   <li>what was found under a thing, written out again at every path that reaches it — one thing
 *       held two ways is two places the answer exposes it;
 *   <li>where the walk is at the moment, so something that reaches itself stops;
 *   <li>how much was opened, which is what says a walk that found nothing looked at something;
 *   <li>and where the walk covered less than it was asked to.
 * </ul>
 *
 * <p><b>What a thing is keyed by, and what a loop means, are not shared.</b> Two objects are the
 * same thing when they are the same object; two types are the same thing when they are the same
 * type with the same letters bound. And a declaration that reaches itself is a shape, which is
 * where that path ends; an object that reaches itself is a graph nobody meant to walk, which is
 * said out loud. Both are asked of whoever is walking.
 *
 * @param <N> what is at a place: an object, or a type with its letters bound
 * @param <P> the way down to it
 */
final class Traversal<N, P extends Trail<P>> {

    /** Why a walk stopped where it did. */
    enum Why {
        /** An array, which says which object it is however its elements compare. */
        AN_ARRAY,
        /** Something that says only which object it is. */
        SAYS_NOTHING_OF_ITSELF,
        /** Something anything may extend or implement, so what stands here is settled by whatever
         *  was put there. */
        NOTHING_CLOSES_IT,
        /** A letter or a wildcard nothing here binds. */
        NOT_BOUND
    }

    /** One place a walk stopped, what was there, and why it stopped. */
    record Stopped<P>(P where, String offender, Why why) {}

    /** What whoever is walking answers, beyond what a thing is. */
    interface Walking<N, P> extends WhatStandsHere.Facts<N, P> {

        /** What tells one thing from another for the purpose of not walking it twice. */
        Object keyOf(N node);

        /** What to call what is here, where a failure names it. */
        String named(N node);

        /**
         * What coming back to where the walk already is means.
         *
         * <p>Null where this path simply ends there, and a gap where it means the walk covered less
         * than it was asked to. Said by whoever is walking, and written by them too: what a gap
         * reads as is the question and the way down to it, and both of those are theirs.
         */
        Gap aLoop(N node, P where);
    }

    private final Walking<N, P> walking;
    private final List<Stopped<P>> out = new ArrayList<>();
    private final List<Gap> gaps = new ArrayList<>();
    /** What was found under each thing, as the way down from that thing. */
    private final Map<Object, List<Stopped<P>>> settled = new LinkedHashMap<>();
    /** What the walk is inside at the moment. */
    private final Set<Object> inside = new LinkedHashSet<>();
    private int opened;

    Traversal(Walking<N, P> walking) {
        this.walking = walking;
    }

    /** Everything found, and where the walk fell short of what it was asked to cover. */
    Covered<Stopped<P>> covered() {
        return Covered.of(List.copyOf(out), List.copyOf(gaps));
    }

    /** How many things the walk went into. */
    int opened() {
        return opened;
    }

    /** Somewhere the walk covered less than it was asked to, said by whoever is walking. */
    void fellShort(Gap gap) {
        gaps.add(gap);
    }

    /**
     * Walk {@code node}, reached at {@code where}.
     *
     * @return whether everything under it was covered, so a caller may remember what was found
     */
    boolean at(N node, P where) {
        // Before anything is asked about it, because what a thing is is worked out by reading it —
        // and a member the walk could not open is a subtree it never asked about, said while the
        // shape is being made rather than while it is being walked.
        int fellShort = gaps.size();
        WhatStandsHere<N, P> what = WhatStandsHere.of(walking, node, where);
        boolean whole = switch (what) {
            case WhatStandsHere.ALanguageValue<N, P> _ -> true;
            case WhatStandsHere.AnArray<N, P> _ -> stop(node, where, Why.AN_ARRAY);
            case WhatStandsHere.SaysNothingOfItself<N, P> _ ->
                    stop(node, where, Why.SAYS_NOTHING_OF_ITSELF);
            case WhatStandsHere.NothingClosesIt<N, P> _ ->
                    stop(node, where, Why.NOTHING_CLOSES_IT);
            case WhatStandsHere.NotBound<N, P> _ -> stop(node, where, Why.NOT_BOUND);
            case WhatStandsHere.AContainerOf<N, P>(List<WhatStandsHere.Under<N, P>> held) ->
                    into(node, where, held, fellShort);
            case WhatStandsHere.ASumOf<N, P>(List<WhatStandsHere.Under<N, P>> arms) ->
                    into(node, where, arms, fellShort);
            case WhatStandsHere.AClosedValue<N, P>(List<WhatStandsHere.Under<N, P>> members) ->
                    into(node, where, members, fellShort);
            case WhatStandsHere.AClosedFamily<N, P>(
                    List<WhatStandsHere.Under<N, P>> members,
                    List<WhatStandsHere.Under<N, P>> arms) -> {
                List<WhatStandsHere.Under<N, P>> both = new ArrayList<>(members);
                both.addAll(arms);
                yield into(node, where, both, fellShort);
            }
        };
        // What was asked about under this is the whole of what is there only where nothing was
        // missed on the way in. A caller that took this as covered would put it away as looked at,
        // and the next path to reach it would be told there was nothing to see.
        return whole && gaps.size() == fellShort;
    }

    /** Said here and gone no further: what is under something that cannot compare is unreachable
     *  through an equality that never holds. */
    private boolean stop(N node, P where, Why why) {
        out.add(new Stopped<>(where, walking.named(node), why));
        return true;
    }

    private boolean into(N node, P where, List<WhatStandsHere.Under<N, P>> under, int fellShort) {
        Object key = walking.keyOf(node);
        List<Stopped<P>> already = settled.get(key);
        if (already != null) {
            already.forEach(each -> out.add(new Stopped<>(
                    where.followedBy(each.where()), each.offender(), each.why())));
            return true;
        }
        if (!inside.add(key)) {
            Gap loop = walking.aLoop(node, where);
            if (loop == null) {
                return true;
            }
            fellShort(loop);
            return false;
        }
        opened++;
        int before = out.size();
        boolean whole = true;
        try {
            for (WhatStandsHere.Under<N, P> each : under) {
                whole &= at(each.node(), each.where());
            }
        } finally {
            inside.remove(key);
        }
        // Everything under it was covered, and reading what it holds missed nothing on the way in.
        if (whole && gaps.size() == fellShort) {
            List<Stopped<P>> mine = new ArrayList<>();
            for (Stopped<P> each : out.subList(before, out.size())) {
                mine.add(new Stopped<>(where.from(each.where()), each.offender(), each.why()));
            }
            settled.put(key, List.copyOf(mine));
        }
        return whole;
    }
}
