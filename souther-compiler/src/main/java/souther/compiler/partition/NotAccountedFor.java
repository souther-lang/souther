package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;

import java.util.Collections;
import java.util.Comparator;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.Set;

/**
 * What a working says it does not account for: each stop it leaves untold at a node of the tree,
 * held by the node it is and with whether asking that node as a quotient by a value accounts for
 * it, and whether anything is left untold that no node is said for.
 *
 * <p>One set answers both questions asked of it, by the same nodes and the same quotients asked:
 * whether anything is left once the quotients a reader asks are taken as accounted for
 * ({@link #isAccountedForBy}), and where what is left is ({@link #whereUnaccountedFor}). So a
 * stop left unresolved is never told at a place that was accounted for, and never told at no
 * place while a place of it is held.
 *
 * <p>A quotient is accounted for by being asked, and only a stop that is the quotient's own
 * ({@link #quotients}): a stop left untold at the same node for anything else
 * ({@link #aStopAt}) is not, so a node held both ways is accounted for by nothing. Something
 * left untold that no node is said for ({@link #andSomethingElse}) is accounted for by nothing
 * either, and keeps every node held beside it.
 *
 * <p>Two put together are the union of what each holds, so putting them together is the same in
 * either order and putting one together with itself changes nothing. Two are equal where they hold
 * the same nodes the same way.
 */
final class NotAccountedFor {

    /** How much a working leaves unaccounted for. */
    enum Kind {
        NOTHING,
        /** The stops of some quotients by a value, each the quotient's own, and nothing else. */
        QUOTIENTS,
        /** Something that is not the stop of a quotient a reader asks. */
        SOMETHING_ELSE
    }

    static final NotAccountedFor NOTHING = new NotAccountedFor(new IdentityHashMap<>(), false);

    /** Places a stop is left untold, in an order that holds whichever texts they are in, and
     *  among two at one place by the node, so that which one is told turns on no order of
     *  putting together. */
    private static final Comparator<Core> STEADILY =
            Comparator.comparing(Core::pos, SourcePos.IN_A_STEADY_ORDER)
                    .thenComparingInt(System::identityHashCode);

    /** Each node a stop is left untold at, and whether asking it as a quotient accounts for it.
     *  Never changed once made. */
    private final IdentityHashMap<Core, Boolean> at;
    /** Whether anything is left untold that no node is said for. */
    private final boolean somethingElse;
    /** What {@link #at} and {@link #somethingElse} come to, said once as they are made. */
    private final Kind kind;

    private NotAccountedFor(IdentityHashMap<Core, Boolean> at, boolean somethingElse) {
        this.at = at;
        this.somethingElse = somethingElse;
        this.kind = (somethingElse || at.containsValue(Boolean.FALSE)) ? Kind.SOMETHING_ELSE
                : at.isEmpty() ? Kind.NOTHING : Kind.QUOTIENTS;
    }

    /** The stops of {@code nodes}, quotients by a value, each the quotient's own; something else
     *  where there are none. */
    static NotAccountedFor quotients(List<Core.Binary> nodes) {
        Gathered out = new Gathered();
        nodes.forEach(out::quotient);
        if (nodes.isEmpty()) {
            out.somethingElse();
        }
        return out.done();
    }

    /** A stop left untold at {@code node}, which asking no quotient accounts for. */
    static NotAccountedFor aStopAt(Core node) {
        Gathered out = new Gathered();
        out.stopAt(node);
        return out.done();
    }

    /** This, and something else beside it that no node is said for, with every node this holds
     *  still held. */
    NotAccountedFor andSomethingElse() {
        return somethingElse ? this : new NotAccountedFor(at, true);
    }

    Kind kind() {
        return kind;
    }

    /** Both put together. */
    NotAccountedFor join(NotAccountedFor other) {
        if (other.holdsNothingBeyond(this)) {
            return this;
        }
        if (holdsNothingBeyond(other)) {
            return other;
        }
        Gathered out = new Gathered();
        out.take(this);
        out.take(other);
        return out.done();
    }

    /** Whether everything {@code this} holds is held by {@code other} as it holds it. */
    private boolean holdsNothingBeyond(NotAccountedFor other) {
        if (somethingElse && !other.somethingElse) {
            return false;
        }
        for (Map.Entry<Core, Boolean> each : at.entrySet()) {
            Boolean there = other.at.get(each.getKey());
            if (there == null || (there && !each.getValue())) {
                return false;
            }
        }
        return true;
    }

    /** Whether this is accounted for by {@code asked}: nothing is left untold but the stops of
     *  quotients that are their own and among {@code asked}. */
    boolean isAccountedForBy(List<Core.Binary> asked) {
        Set<Core> askedOnce = byNode(asked);
        return !somethingElse && at.keySet().stream()
                .allMatch(each -> accountedFor(each, askedOnce));
    }

    /**
     * Where a stop is left untold that {@code asked} does not account for: of the nodes held, the
     * first {@link #STEADILY} that is not accounted for as {@link #isAccountedForBy} asks it. None
     * where every node is, though something else may still be left that no node is said for.
     */
    Optional<Core> whereUnaccountedFor(List<Core.Binary> asked) {
        Set<Core> askedOnce = byNode(asked);
        return at.keySet().stream().filter(each -> !accountedFor(each, askedOnce)).min(STEADILY);
    }

    private boolean accountedFor(Core node, Set<Core> asked) {
        return at.get(node) && asked.contains(node);
    }

    /** {@code asked}, by the node each is, to be asked of each node held at the same cost. */
    private static Set<Core> byNode(List<Core.Binary> asked) {
        Set<Core> out = Collections.newSetFromMap(new IdentityHashMap<>());
        out.addAll(asked);
        return out;
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof NotAccountedFor that && somethingElse == that.somethingElse
                && at.equals(that.at);
    }

    @Override
    public int hashCode() {
        return at.hashCode() * 2 + (somethingElse ? 1 : 0);
    }

    @Override
    public String toString() {
        return kind() + (at.isEmpty() ? "" : ", untold at " + at.size());
    }

    /**
     * What a reading leaves untold as it goes, gathered one stop at a time and taken as a
     * {@link NotAccountedFor} where the reading is done: each stop added costs the same however
     * many are held, where a value made again for each would cost all of them.
     */
    static final class Gathered {

        private IdentityHashMap<Core, Boolean> at = new IdentityHashMap<>();
        private boolean somethingElse;
        /** What was last taken, while nothing has been added since; null otherwise. */
        private NotAccountedFor taken;

        /** That a stop is left untold at {@code node}, which asking no quotient accounts for. */
        void stopAt(Core node) {
            put(Core.withoutStanding(node), false);
        }

        /** That the stop of {@code quotient}, its own, is left untold. */
        void quotient(Core.Binary quotient) {
            put(quotient, true);
        }

        /** That something is left untold that no node is said for. */
        void somethingElse() {
            if (!somethingElse) {
                changing();
                somethingElse = true;
            }
        }

        /** Everything {@code other} holds, as it holds it. */
        void take(NotAccountedFor other) {
            other.at.forEach(this::put);
            if (other.somethingElse) {
                somethingElse();
            }
        }

        /** Everything {@code other} holds, as it holds it. */
        void take(Gathered other) {
            take(other.done());
        }

        private void put(Core node, boolean accountable) {
            Boolean had = at.get(node);
            boolean now = had == null ? accountable : had && accountable;
            if (had == null || had != now) {
                changing();
                at.put(node, now);
            }
        }

        private void changing() {
            if (taken != null) {
                at = new IdentityHashMap<>(at);
                taken = null;
            }
        }

        /** What has been gathered, as it stands. */
        NotAccountedFor done() {
            if (taken == null) {
                taken = new NotAccountedFor(at, somethingElse);
            }
            return taken;
        }
    }
}
