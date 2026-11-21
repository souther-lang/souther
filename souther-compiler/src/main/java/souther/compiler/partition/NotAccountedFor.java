package souther.compiler.partition;

import souther.compiler.core.Core;

import java.util.ArrayList;
import java.util.List;

/**
 * What a working says it does not account for: nothing, the stops of some quotients by a value
 * and nothing else, or something no reader can name.
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

    static final NotAccountedFor NOTHING = new NotAccountedFor(Kind.NOTHING, List.of());

    static final NotAccountedFor SOMETHING_ELSE = new NotAccountedFor(Kind.SOMETHING_ELSE,
            List.of());

    private final Kind kind;
    private final List<Core.Binary> quotients;

    /** The quotients are a set of nodes: each once, by the node it is. */
    private NotAccountedFor(Kind kind, List<Core.Binary> quotients) {
        this.kind = kind;
        List<Core.Binary> distinct = new ArrayList<>();
        for (Core.Binary each : quotients) {
            if (distinct.stream().noneMatch(one -> one == each)) {
                distinct.add(each);
            }
        }
        this.quotients = List.copyOf(distinct);
    }

    /** The stops of {@code nodes}, quotients by a value, and nothing else; something else where
     *  there are none. */
    static NotAccountedFor quotients(List<Core.Binary> nodes) {
        return nodes.isEmpty() ? SOMETHING_ELSE
                : new NotAccountedFor(Kind.QUOTIENTS, List.copyOf(nodes));
    }

    Kind kind() {
        return kind;
    }

    /** Both put together. */
    NotAccountedFor join(NotAccountedFor other) {
        if (kind == Kind.NOTHING) {
            return other;
        }
        if (other.kind == Kind.NOTHING) {
            return this;
        }
        if (kind == Kind.SOMETHING_ELSE || other.kind == Kind.SOMETHING_ELSE) {
            return SOMETHING_ELSE;
        }
        List<Core.Binary> both = new ArrayList<>(quotients);
        both.addAll(other.quotients);
        return new NotAccountedFor(Kind.QUOTIENTS, both);
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
                && quotients.size() == that.quotients.size()
                && quotients.stream().allMatch(that::names);
    }

    @Override
    public int hashCode() {
        int sum = kind.hashCode();
        for (Core.Binary each : quotients) {
            sum += System.identityHashCode(each);
        }
        return sum;
    }

    @Override
    public String toString() {
        return kind == Kind.QUOTIENTS ? "quotients " + quotients.size() : kind.toString();
    }
}
