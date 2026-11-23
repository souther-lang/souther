package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Optional;

/**
 * What a working says it does not account for: nothing, the stops of some quotients by a value
 * and nothing else, or something no reader can name; and, beside any of these, every place a
 * stop is left untold, where the readings that left them found the expressions.
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
 * <p>The places a stop is left untold are kept whole, and the places of two put together are the
 * places of both, so nothing is chosen of them before what is accounted for is known. Which one a
 * reader is told is asked with what accounts for the rest ({@link #whereUnaccountedFor}), as
 * whether anything is left is ({@link #isAccountedForBy}). Something else is only ever made from
 * what was left before ({@link #andSomethingElse}), so no reader widening what is left drops a
 * place it held.
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

    /** Places a stop is left untold, in an order that holds whichever texts they are in and
     *  whatever order they were met in. */
    private static final Comparator<Core> STEADILY =
            Comparator.comparing(Core::pos, SourcePos.IN_A_STEADY_ORDER);

    private final Kind kind;
    private final List<Core.Binary> quotients;
    private final List<Core> untoldAt;

    /** The quotients are a set of nodes, each once by the node it is; the places a set of where
     *  each is written, each once by its place, since that is what is said of one. */
    private NotAccountedFor(Kind kind, List<Core.Binary> quotients, List<? extends Core> at) {
        this.kind = kind;
        List<Core.Binary> distinct = new ArrayList<>();
        for (Core.Binary each : quotients) {
            if (distinct.stream().noneMatch(one -> one == each)) {
                distinct.add(each);
            }
        }
        this.quotients = List.copyOf(distinct);
        List<Core> places = new ArrayList<>();
        for (Core each : at) {
            if (places.stream().noneMatch(one -> one.pos().equals(each.pos()))) {
                places.add(each);
            }
        }
        this.untoldAt = List.copyOf(places);
    }

    /** The stops of {@code nodes}, quotients by a value, and nothing else; something else where
     *  there are none. Each is where a stop is left untold. */
    static NotAccountedFor quotients(List<Core.Binary> nodes) {
        return nodes.isEmpty() ? SOMETHING_ELSE
                : new NotAccountedFor(Kind.QUOTIENTS, nodes, List.copyOf(nodes));
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

    /**
     * Where a stop is left untold that {@code asked} does not account for, which is the one a
     * reader is told where {@link #isAccountedForBy} says something is left: of the places, the
     * first {@link #STEADILY} that is no quotient among {@code asked}. Asked of the same quotients
     * as whether anything is left, so the place told is one of what is left and never a stop
     * already accounted for. None where every place is one of them, or none was found.
     */
    Optional<Core> whereUnaccountedFor(List<Core.Binary> asked) {
        return untoldAt.stream()
                .filter(each -> asked.stream().noneMatch(one -> one == each))
                .min(STEADILY);
    }

    /** Whether this names {@code node}, a quotient, as one of those it leaves. */
    boolean names(Core.Binary node) {
        return kind == Kind.QUOTIENTS && quotients.stream().anyMatch(one -> one == node);
    }

    /** The places are told apart by where each is written, which is what is said of one. */
    @Override
    public boolean equals(Object other) {
        return other instanceof NotAccountedFor that && kind == that.kind
                && quotients.size() == that.quotients.size()
                && quotients.stream().allMatch(that::names)
                && untoldAt.size() == that.untoldAt.size()
                && untoldAt.stream().allMatch(each -> that.untoldAt.stream()
                        .anyMatch(one -> one.pos().equals(each.pos())));
    }

    @Override
    public int hashCode() {
        int sum = kind.hashCode();
        for (Core.Binary each : quotients) {
            sum += System.identityHashCode(each);
        }
        for (Core each : untoldAt) {
            sum += each.pos().hashCode();
        }
        return sum;
    }

    @Override
    public String toString() {
        String said = kind == Kind.QUOTIENTS ? "quotients " + quotients.size() : kind.toString();
        return untoldAt.isEmpty() ? said : said + ", untold at " + untoldAt.size();
    }
}
