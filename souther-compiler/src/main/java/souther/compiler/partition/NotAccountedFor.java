package souther.compiler.partition;

import souther.compiler.core.Core;

import java.util.ArrayList;
import java.util.List;

/**
 * What a working says it does not account for: nothing, the stops of some quotients by a value
 * and nothing else, or something no reader can name; and, beside any of these, where each stop it
 * leaves untold is, where the reading that left it found the expression.
 *
 * <p>The quotients are named by the node of the expression they are, so that a reader that judges
 * the quotients a comparison always works out ({@link QuotientsEveryRunWorksOut}) can take what
 * is left to them as accounted for, and only those. A quotient is accounted for by being asked, so
 * what a working leaves to a quotient that is not asked is left to something else.
 *
 * <p>Two of these put together are their join: nothing is the identity, something else absorbs
 * everything, and quotients with quotients are the quotients of both. No other combination is
 * made, so what one working leaves to something else cannot be recovered by putting it beside one
 * that leaves only quotients.
 *
 * <p>Where a stop is left untold is said for a reader to name, and accounts for nothing: the
 * places of two put together are the places of both, whatever else either leaves. Something else
 * is only ever made from what was left before ({@link #andSomethingElse}), so no reader widening
 * what is left drops a place it held.
 */
final class NotAccountedFor {

    /** How much a working leaves unaccounted for. */
    enum Kind {
        NOTHING,
        /** The stops of the quotients {@link #quotients}, and nothing else. */
        QUOTIENTS,
        /** Something that is not the stop of a quotient a reader asks. */
        SOMETHING_ELSE
    }

    static final NotAccountedFor NOTHING = new NotAccountedFor(Kind.NOTHING, List.of(),
            List.of());

    /** Something else and no place: not handed out, for the reason the class says. */
    private static final NotAccountedFor SOMETHING_ELSE = new NotAccountedFor(
            Kind.SOMETHING_ELSE, List.of(), List.of());

    private final Kind kind;
    private final List<Core.Binary> quotients;
    private final List<Core> untoldAt;

    /** The quotients and the places are sets of nodes: each once, by the node it is, in the order
     *  first met. */
    private NotAccountedFor(Kind kind, List<? extends Core> quotients, List<? extends Core> at) {
        this.kind = kind;
        this.quotients = distinct(quotients).stream().map(Core.Binary.class::cast).toList();
        this.untoldAt = distinct(at);
    }

    private static List<Core> distinct(List<? extends Core> nodes) {
        if (nodes.isEmpty()) {
            return List.of();
        }
        List<Core> out = new ArrayList<>();
        for (Core each : nodes) {
            if (out.stream().noneMatch(one -> one == each)) {
                out.add(each);
            }
        }
        return List.copyOf(out);
    }

    /** The stops of {@code nodes}, quotients by a value, and nothing else; something else where
     *  there are none. Each is where a stop is left untold. */
    static NotAccountedFor quotients(List<Core.Binary> nodes) {
        return nodes.isEmpty() ? SOMETHING_ELSE
                : new NotAccountedFor(Kind.QUOTIENTS, nodes, nodes);
    }

    /** A stop left untold at {@code node}, which is something else. */
    static NotAccountedFor aStopAt(Core node) {
        return new NotAccountedFor(Kind.SOMETHING_ELSE, List.of(), List.of(node));
    }

    /** This, and something else beside it: what a reader leaves where it cannot name what is
     *  left, with every place this holds still held. */
    NotAccountedFor andSomethingElse() {
        return join(SOMETHING_ELSE);
    }

    Kind kind() {
        return kind;
    }

    /** Where each stop left untold is, in the order first met: the expressions whose own working
     *  may end a run, as the readings that left them found them, and not every one there may be. */
    List<Core> untoldAt() {
        return untoldAt;
    }

    /** Both put together. */
    NotAccountedFor join(NotAccountedFor other) {
        if (kind == Kind.NOTHING && untoldAt.isEmpty()) {
            return other;
        }
        if (other.kind == Kind.NOTHING && other.untoldAt.isEmpty()) {
            return this;
        }
        List<Core> at = both(untoldAt, other.untoldAt);
        if (kind == Kind.SOMETHING_ELSE || other.kind == Kind.SOMETHING_ELSE) {
            return at.isEmpty() ? SOMETHING_ELSE
                    : new NotAccountedFor(Kind.SOMETHING_ELSE, List.of(), at);
        }
        return new NotAccountedFor(Kind.QUOTIENTS, both(quotients, other.quotients), at);
    }

    private static <T> List<T> both(List<T> one, List<T> other) {
        if (other.isEmpty()) {
            return one;
        }
        if (one.isEmpty()) {
            return other;
        }
        List<T> out = new ArrayList<>(one);
        out.addAll(other);
        return out;
    }

    /** Whether this is accounted for by {@code asked}: nothing is left, or only the stops of
     *  quotients every one of which is among them. */
    boolean isAccountedForBy(List<Core.Binary> asked) {
        return switch (kind) {
            case NOTHING -> true;
            case QUOTIENTS -> quotients.stream().allMatch(each -> asked.stream()
                    .anyMatch(one -> one == each));
            case SOMETHING_ELSE -> false;
        };
    }

    /** Whether this names {@code node}, a quotient, as one of those it leaves. */
    boolean names(Core.Binary node) {
        return kind == Kind.QUOTIENTS && quotients.stream().anyMatch(one -> one == node);
    }

    @Override
    public boolean equals(Object other) {
        return other instanceof NotAccountedFor that && kind == that.kind
                && sameNodes(quotients, that.quotients) && sameNodes(untoldAt, that.untoldAt);
    }

    private static boolean sameNodes(List<? extends Core> one, List<? extends Core> other) {
        return one.size() == other.size()
                && one.stream().allMatch(each -> other.stream().anyMatch(that -> that == each));
    }

    @Override
    public int hashCode() {
        int sum = kind.hashCode();
        for (Core each : quotients) {
            sum += System.identityHashCode(each);
        }
        for (Core each : untoldAt) {
            sum += System.identityHashCode(each);
        }
        return sum;
    }

    @Override
    public String toString() {
        String said = kind == Kind.QUOTIENTS ? "quotients " + quotients.size() : kind.toString();
        return untoldAt.isEmpty() ? said : said + ", untold at " + untoldAt.size();
    }
}
