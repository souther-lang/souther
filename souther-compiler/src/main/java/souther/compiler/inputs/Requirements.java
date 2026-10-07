package souther.compiler.inputs;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What has to be true of a value for a position to exist in it, or for a class to hold there.
 *
 * <p>Read off a path and never kept beside one. {@code query@GlobalQuery.tag} says that
 * {@code query} is a {@code GlobalQuery} and says it completely; a position carrying that fact a
 * second time would be two accounts of one thing, waiting to disagree.
 *
 * <p><b>One merge decides every compatibility.</b> Whether two classes can be asked for in one row,
 * whether a pair of them is a combination the model has at all, and what a value being built has to
 * be are the same question asked by three readers. Answered separately, each would work out for
 * itself that a row cannot be a {@code FeedQuery} and have a {@code GlobalQuery}'s {@code tag} — and
 * the coverage denominator and the generator disagreeing about which combinations exist is how a
 * report comes to ask for rows nothing can write.
 *
 * <p><b>What is required at a position is the cases it is left, and two requirements of one
 * position are both of them.</b> A value the outer arm leaves {@code Station} or {@code Hospital}
 * and the inner arm leaves {@code Station} is a {@code Station}, so the two hold together and what
 * holds is the stronger one. They disagree only where they leave the position no case in common.
 *
 * <p><b>A requirement may be stated at a name the cases of a sum share, and it moves under the case
 * once one is chosen.</b> A fork on {@code r.q.flag} asks something of the value at that name, and
 * the value stands at {@code r.q@A.flag} or at {@code r.q@B.flag} depending on which case
 * {@code r.q} turns out to be ({@link NameReach#standingOf}). Until something here says which, the
 * requirement stays at the name: choosing a case for it would be a narrowing nobody asked for. Once
 * {@code r.q} is required to be {@code A}, the requirement is the one at {@code r.q@A.flag}, and is
 * met against whatever else is required there — so a way asking {@code Yes} at the name and a class
 * asking {@code No} under {@code A} are a conflict, found by the same merge as any other.
 *
 * <p>The crossings are what moves it, and they travel here rather than with whoever merges: every
 * reader that puts two requirements together asks {@link #merge}, and a name that moved for one of
 * them and not another would be one requirement with two answers. Only the crossings some name
 * here still has to cross are kept, so a requirement whose names have all moved is the requirement
 * written at the positions, with nothing beside it.
 *
 * <p><b>A set of crossings, held in one order.</b> This is a conjunction, so two of them put
 * together either way round are one value, and so are three put together in either grouping.
 * The positions are a map and compare as one; the crossings are kept in an order of their own —
 * the sum's position, outer before inner, then the name, the case and where it stands — so that
 * neither which side brought a crossing nor which was merged first is part of what this is.
 *
 * @param crossings where the names among {@code refinements} stand once the sum above each is a
 *                  case of it
 */
public record Requirements(Map<TermPath, CasesLeft> refinements,
                           List<NameReach.Crossing> crossings) {

    /** The one order crossings are held in, which ties no two that are not equal. */
    private static final Comparator<NameReach.Crossing> CROSSING_ORDER =
            Comparator.comparing(NameReach.Crossing::at, TermPath.structuralOrder())
                    .thenComparing(NameReach.Crossing::field)
                    .thenComparing((one, other) -> CasesLeft.compare(CasesLeft.of(one.branch()),
                            CasesLeft.of(other.branch())))
                    .thenComparing(NameReach.Crossing::to, TermPath.structuralOrder());

    /** Nothing has to be true: a position under no refinement, or a class that selects none. */
    public static final Requirements NONE = new Requirements(Map.of(), List.of());

    public Requirements {
        // The order they were reached in, outermost first, which is the order a reason about them
        // reads in.
        refinements = Collections.unmodifiableMap(new LinkedHashMap<>(refinements));
        crossings = stillToCross(refinements, crossings);
        for (NameReach.Crossing each : crossings) {
            for (TermPath name : refinements.keySet()) {
                if (each.standingUnderTheCase(name) != null && decides(refinements, each)) {
                    throw new IllegalArgumentException("`" + name + "` is required at the name"
                            + " while `" + each.at() + "` is required to be "
                            + each.branch().spelled() + ", where the name stands at `"
                            + each.standingUnderTheCase(name) + "`; a requirement is moved under"
                            + " the case where the case is chosen");
                }
            }
        }
    }

    /**
     * What has to be true for {@code path} to exist, where every name it steps through stands where
     * {@code crossings} say once the sum above it is a case.
     *
     * <p>{@link TermPath#requirements} for a path that steps through a name the cases share. The
     * path itself writes the name, and whatever already settles a case moves it: a path under a
     * narrowing to {@code A} reads the name where {@code A} holds it.
     */
    public static Requirements of(TermPath path, List<NameReach.Crossing> crossings) {
        return switch (moved(path.requirements().refinements, crossings)) {
            case Merge.Merged(Requirements moved) -> moved;
            case Merge.Conflict conflict -> throw new IllegalArgumentException(
                    "`" + path + "` requires `" + conflict.at() + "` to be both "
                            + conflict.one().spelled() + " and " + conflict.other().spelled());
        };
    }

    /** The crossings some name among {@code refinements} still stands above, each once and in
     *  {@link #CROSSING_ORDER}. */
    private static List<NameReach.Crossing> stillToCross(Map<TermPath, CasesLeft> refinements,
                                                         List<NameReach.Crossing> crossings) {
        if (crossings.isEmpty()) {
            return List.of();
        }
        // A crossing a name crosses after another one moved it is still to cross: what is kept is
        // every crossing reachable from the names as they stand.
        Set<TermPath> names = new LinkedHashSet<>(refinements.keySet());
        Set<NameReach.Crossing> kept = new LinkedHashSet<>();
        boolean grew = true;
        while (grew) {
            grew = false;
            for (NameReach.Crossing each : crossings) {
                for (TermPath name : List.copyOf(names)) {
                    TermPath to = each.standingUnderTheCase(name);
                    if (to != null) {
                        grew |= kept.add(each);
                        grew |= names.add(to);
                    }
                }
            }
        }
        return canonical(kept);
    }

    /** {@code crossings} each once and in {@link #CROSSING_ORDER}. */
    private static List<NameReach.Crossing> canonical(Collection<NameReach.Crossing> crossings) {
        List<NameReach.Crossing> out = new ArrayList<>(new LinkedHashSet<>(crossings));
        out.sort(CROSSING_ORDER);
        return List.copyOf(out);
    }

    /** Whether {@code refinements} leaves the sum {@code crossing} is about only its case. */
    private static boolean decides(Map<TermPath, CasesLeft> refinements,
                                   NameReach.Crossing crossing) {
        CasesLeft atTheSum = refinements.get(crossing.at());
        return atTheSum != null && atTheSum.within(CasesLeft.of(crossing.branch()));
    }

    /**
     * The same, with {@code refinement} required at {@code at} — which is what a class selecting one
     * adds to what its position's path already required.
     *
     * <p><b>A fact already known to hold, and not a question about whether it does.</b> Whether two
     * requirements can be met at once is {@link #merge}'s to answer and nothing else's, so this
     * takes what its caller has established: a position's path requires nothing at the position
     * itself, and a class of it selects there. Asked to put a second narrowing where one already
     * stands, this refuses rather than keeping either — a requirement that contradicts itself is met
     * by no value, and would have a row reported impossible with nothing having decided that.
     */
    public Requirements and(TermPath at, Refinement refinement) {
        return refinement == null ? this : and(at, CasesLeft.of(refinement));
    }

    /** The same, with the position at {@code at} left {@code cases}. */
    public Requirements and(TermPath at, CasesLeft cases) {
        CasesLeft had = refinements.get(at);
        if (cases.equals(had)) {
            return this;
        }
        if (had != null) {
            throw new IllegalArgumentException(
                    "`" + at + "` is required to be " + had.spelled() + " and asked to be "
                            + cases.spelled() + "; whether two requirements hold together is"
                            + " what merging them answers");
        }
        Map<TermPath, CasesLeft> wider = new LinkedHashMap<>(refinements);
        wider.put(at, cases);
        // Choosing the case may move a name stated above it, and the name moved may meet what is
        // already stated under the case.
        return switch (moved(wider, crossings)) {
            case Merge.Merged(Requirements both) -> both;
            case Merge.Conflict conflict -> throw new IllegalArgumentException(
                    "`" + at + "` asked to be " + cases.spelled() + " moves a requirement to `"
                            + conflict.at() + "`, which is required to be "
                            + conflict.one().spelled() + " and " + conflict.other().spelled()
                            + "; whether two requirements hold together is what merging them"
                            + " answers");
        };
    }

    /**
     * The names something is required of that stand under the cases of a sum nothing here has
     * chosen a case of, outer before inner.
     *
     * <p>What a writer still has to choose a case for: a row is one case of every sum, and until
     * that is said a requirement at one of these is about no position the row writes. In the order
     * of the paths and not the order they were merged in, since the writer tries the cases in this
     * order and the first that composes is the row.
     */
    public List<TermPath> atANameTheCasesShare() {
        List<TermPath> out = new ArrayList<>();
        for (TermPath name : refinements.keySet()) {
            for (NameReach.Crossing each : crossings) {
                if (each.standingUnderTheCase(name) != null) {
                    out.add(name);
                    break;
                }
            }
        }
        out.sort(TermPath.structuralOrder());
        return List.copyOf(out);
    }

    /** What is required at {@code at}, or null where nothing is. */
    public CasesLeft at(TermPath at) {
        return refinements.get(at);
    }

    /**
     * Both, or the position they disagree about.
     *
     * <p>Two requirements are compatible exactly when every position both of them speak of is left
     * some case by each of them in common, and what is required there afterwards is those cases. A
     * position one of them says nothing about is one the other settles alone: a row is free to be
     * whatever it likes where nothing asked.
     *
     * <p>A requirement at a name the cases share is about the position it stands at once the case
     * is chosen, so one side choosing the case moves what the other side stated at the name, and
     * what moved is met at the position it moved to.
     */
    public Merge merge(Requirements other) {
        if (other.refinements.isEmpty()) {
            return new Merge.Merged(this);
        }
        Map<TermPath, CasesLeft> both = new LinkedHashMap<>(refinements);
        for (Map.Entry<TermPath, CasesLeft> each : other.refinements.entrySet()) {
            Merge.Conflict conflict = meetInto(both, each.getKey(), each.getValue());
            if (conflict != null) {
                return conflict;
            }
        }
        List<NameReach.Crossing> all = crossings;
        if (!other.crossings.isEmpty()) {
            List<NameReach.Crossing> wider = new ArrayList<>(crossings);
            wider.addAll(other.crossings);
            all = wider;
        }
        return moved(both, all);
    }

    /**
     * {@code refinements} with every name a chosen case decides moved under that case, or the
     * position where what moved meets something it cannot be.
     *
     * <p>Run until nothing moves, because a name under two sums is moved by the outer one before
     * the inner one can see it. Bounded by the crossings: each move takes a name one crossing
     * down, and no name is above the same crossing twice.
     */
    private static Merge moved(Map<TermPath, CasesLeft> refinements,
                               List<NameReach.Crossing> crossings) {
        if (crossings.isEmpty()) {
            return new Merge.Merged(new Requirements(refinements, crossings));
        }
        // Outer before inner and in one order whichever side brought them, so that where a moved
        // requirement is found to conflict does not turn on which was merged first.
        List<NameReach.Crossing> ordered = canonical(crossings);
        Map<TermPath, CasesLeft> out = new LinkedHashMap<>(refinements);
        int moves = 0;
        boolean moving = true;
        while (moving) {
            moving = false;
            for (NameReach.Crossing each : ordered) {
                if (!decides(out, each)) {
                    continue;
                }
                for (TermPath name : List.copyOf(out.keySet())) {
                    TermPath to = each.standingUnderTheCase(name);
                    if (to == null) {
                        continue;
                    }
                    if (++moves > ordered.size() * Math.max(1, refinements.size())) {
                        throw new IllegalStateException("a requirement was moved past every"
                                + " crossing it could take: " + name);
                    }
                    CasesLeft asked = out.remove(name);
                    Merge.Conflict conflict = meetInto(out, to, asked);
                    if (conflict != null) {
                        return conflict;
                    }
                    moving = true;
                }
            }
        }
        return new Merge.Merged(new Requirements(out, ordered));
    }

    /** {@code cases} met at {@code at} in {@code into}, or the conflict where they share none. */
    private static Merge.Conflict meetInto(Map<TermPath, CasesLeft> into, TermPath at,
                                           CasesLeft cases) {
        CasesLeft had = into.get(at);
        if (had == null) {
            into.put(at, cases);
            return null;
        }
        CasesLeft common = had.meet(cases);
        if (common == null) {
            return new Merge.Conflict(at, had, cases);
        }
        into.put(at, common);
        return null;
    }

    /** Whether the two can hold of one value. */
    public boolean compatibleWith(Requirements other) {
        return merge(other) instanceof Merge.Merged;
    }

    /** What came of putting two requirements together. */
    public sealed interface Merge {

        /** They hold together, and this is what holds. */
        record Merged(Requirements requirements) implements Merge {}

        /**
         * They do not, and this is the position that cannot be both.
         *
         * <p>Which position, and which two, because that is what a report of an absent combination
         * is about: a pair left out of the denominator is left out for a reason an author can read.
         */
        record Conflict(TermPath at, CasesLeft one, CasesLeft other) implements Merge {}
    }
}
