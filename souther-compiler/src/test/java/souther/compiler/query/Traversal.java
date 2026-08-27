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

    /**
     * Walk {@code node}, reached at {@code where}.
     *
     * @return whether everything under it was covered, so a caller may remember what was found
     */
    boolean at(N node, P where) {
        return switch (WhatStandsHere.of(walking, node, where)) {
            case WhatStandsHere.ALanguageValue<N, P> _ -> true;
            case WhatStandsHere.AnArray<N, P> _ -> stop(node, where, Why.AN_ARRAY);
            case WhatStandsHere.SaysNothingOfItself<N, P> _ ->
                    stop(node, where, Why.SAYS_NOTHING_OF_ITSELF);
            case WhatStandsHere.NothingClosesIt<N, P> _ ->
                    stop(node, where, Why.NOTHING_CLOSES_IT);
            case WhatStandsHere.NotBound<N, P> _ -> stop(node, where, Why.NOT_BOUND);
            case WhatStandsHere.AContainerOf<N, P>(Covered<WhatStandsHere.Under<N, P>> held) ->
                    into(node, where, held);
            case WhatStandsHere.ASumOf<N, P>(Covered<WhatStandsHere.Under<N, P>> arms) ->
                    into(node, where, arms);
            case WhatStandsHere.AClosedValue<N, P>(Covered<WhatStandsHere.Under<N, P>> members) ->
                    into(node, where, members);
            case WhatStandsHere.AClosedFamily<N, P>(
                    Covered<WhatStandsHere.Under<N, P>> members,
                    Covered<WhatStandsHere.Under<N, P>> arms) ->
                    into(node, where, both(members, arms));
        };
    }

    /** What a family holds and what stands under it, which are each ways down from it. */
    private static <N, P> Covered<WhatStandsHere.Under<N, P>> both(
            Covered<WhatStandsHere.Under<N, P>> members,
            Covered<WhatStandsHere.Under<N, P>> arms) {
        List<WhatStandsHere.Under<N, P>> found = new ArrayList<>(ways(members));
        found.addAll(ways(arms));
        List<Gap> fellShort = new ArrayList<>(shortOf(members));
        fellShort.addAll(shortOf(arms));
        return Covered.of(List.copyOf(found), List.copyOf(fellShort));
    }

    private static <N, P> List<WhatStandsHere.Under<N, P>> ways(
            Covered<WhatStandsHere.Under<N, P>> under) {
        return switch (under) {
            case Covered.Whole<WhatStandsHere.Under<N, P>>(
                    List<WhatStandsHere.Under<N, P>> all) -> all;
            case Covered.Partly<WhatStandsHere.Under<N, P>>(
                    List<WhatStandsHere.Under<N, P>> all, List<Gap> _) -> all;
        };
    }

    private static <N, P> List<Gap> shortOf(Covered<WhatStandsHere.Under<N, P>> under) {
        return switch (under) {
            case Covered.Whole<WhatStandsHere.Under<N, P>> _ -> List.of();
            case Covered.Partly<WhatStandsHere.Under<N, P>>(
                    List<WhatStandsHere.Under<N, P>> _, List<Gap> fellShort) -> fellShort;
        };
    }

    /** Said here and gone no further: what is under something that cannot compare is unreachable
     *  through an equality that never holds. */
    private boolean stop(N node, P where, Why why) {
        out.add(new Stopped<>(where, walking.named(node), why));
        return true;
    }

    /**
     * Into what a thing holds, where reading it says whether that is all of it.
     *
     * <p>What comes back says both, and only one of them is about the walking: a way down that was
     * never read is a subtree nothing asked about, and a thing that holds one of those is a thing
     * this got part way into however well the rest of it went.
     */
    private boolean into(N node, P where, Covered<WhatStandsHere.Under<N, P>> under) {
        List<Gap> fellShort = shortOf(under);
        gaps.addAll(fellShort);
        Object key = walking.keyOf(node);
        List<Stopped<P>> already = settled.get(key);
        if (already != null) {
            already.forEach(each -> out.add(new Stopped<>(
                    where.followedBy(each.where()), each.offender(), each.why())));
            return fellShort.isEmpty();
        }
        if (!inside.add(key)) {
            Gap loop = walking.aLoop(node, where);
            if (loop == null) {
                return fellShort.isEmpty();
            }
            gaps.add(loop);
            return false;
        }
        opened++;
        int before = out.size();
        boolean whole = fellShort.isEmpty();
        try {
            for (WhatStandsHere.Under<N, P> each : ways(under)) {
                whole &= at(each.node(), each.where());
            }
        } finally {
            inside.remove(key);
        }
        // Everything under it was covered, and reading what it holds missed nothing.
        if (whole) {
            List<Stopped<P>> mine = new ArrayList<>();
            for (Stopped<P> each : out.subList(before, out.size())) {
                mine.add(new Stopped<>(where.from(each.where()), each.offender(), each.why()));
            }
            settled.put(key, List.copyOf(mine));
        }
        return whole;
    }
}
