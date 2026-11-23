package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;

import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Objects;
import java.util.Optional;

/**
 * What a working says it does not account for: nothing, the stops of some quotients by a value
 * and nothing else, or something no reader can name; and, beside any of these, where the first
 * stop it leaves untold is, where the reading that left it found the expression.
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
 * <p>Where a stop is left untold is said for a reader to name, and accounts for nothing. It is one
 * such place, as a proof that a run gets past names the place it gave out at: of two put together,
 * the one written first ({@link SourcePos#IN_WRITTEN_ORDER}), which is what an author reads first
 * and does not turn on the order the readings were made in. Something else is only ever made from
 * what was left before ({@link #andSomethingElse}), so no reader widening what is left drops the
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

    static final NotAccountedFor NOTHING = new NotAccountedFor(Kind.NOTHING, List.of(), null);

    /** Something else and no place: not handed out, for the reason the class says. */
    private static final NotAccountedFor SOMETHING_ELSE = new NotAccountedFor(
            Kind.SOMETHING_ELSE, List.of(), null);

    private final Kind kind;
    private final List<Core.Binary> quotients;
    /** The first place a stop is left untold, or null where none is said. */
    private final Core untoldAt;

    /** The quotients are a set of nodes: each once, by the node it is. */
    private NotAccountedFor(Kind kind, List<Core.Binary> quotients, Core untoldAt) {
        this.kind = kind;
        List<Core.Binary> distinct = new ArrayList<>();
        for (Core.Binary each : quotients) {
            if (distinct.stream().noneMatch(one -> one == each)) {
                distinct.add(each);
            }
        }
        this.quotients = List.copyOf(distinct);
        this.untoldAt = untoldAt;
    }

    /** The stops of {@code nodes}, quotients by a value, and nothing else; something else where
     *  there are none. Each is where a stop is left untold. */
    static NotAccountedFor quotients(List<Core.Binary> nodes) {
        return nodes.isEmpty() ? SOMETHING_ELSE : new NotAccountedFor(Kind.QUOTIENTS, nodes,
                nodes.stream().min(WRITTEN_FIRST).orElseThrow());
    }

    /** Two places a stop is left untold, the one written first first. */
    private static final Comparator<Core> WRITTEN_FIRST =
            Comparator.comparing(Core::pos, SourcePos.IN_WRITTEN_ORDER);

    /** A stop left untold at {@code node}, which is something else. */
    static NotAccountedFor aStopAt(Core node) {
        return new NotAccountedFor(Kind.SOMETHING_ELSE, List.of(), node);
    }

    /** This, and something else beside it: what a reader leaves where it cannot name what is
     *  left, with the place this holds still held. */
    NotAccountedFor andSomethingElse() {
        return join(SOMETHING_ELSE);
    }

    Kind kind() {
        return kind;
    }

    /** Where the stop left untold written first is: the expression whose own working may end a
     *  run, as the reading that left it found it, and not every one there may be. */
    Optional<Core> untoldAt() {
        return Optional.ofNullable(untoldAt);
    }

    /** Both put together. */
    NotAccountedFor join(NotAccountedFor other) {
        if (kind == Kind.NOTHING && untoldAt == null) {
            return other;
        }
        if (other.kind == Kind.NOTHING && other.untoldAt == null) {
            return this;
        }
        Core at = untoldAt == null ? other.untoldAt
                : other.untoldAt == null || WRITTEN_FIRST.compare(untoldAt, other.untoldAt) <= 0
                ? untoldAt : other.untoldAt;
        if (kind == Kind.SOMETHING_ELSE || other.kind == Kind.SOMETHING_ELSE) {
            return at == null ? SOMETHING_ELSE
                    : new NotAccountedFor(Kind.SOMETHING_ELSE, List.of(), at);
        }
        List<Core.Binary> both = new ArrayList<>(quotients);
        both.addAll(other.quotients);
        return new NotAccountedFor(Kind.QUOTIENTS, both, at);
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

    /** The place is told apart by where it is written, which is what is said of it: two nodes
     *  written at one place are one place, whichever of them a join kept. */
    @Override
    public boolean equals(Object other) {
        return other instanceof NotAccountedFor that && kind == that.kind
                && quotients.size() == that.quotients.size()
                && quotients.stream().allMatch(that::names)
                && Objects.equals(placeOf(untoldAt), placeOf(that.untoldAt));
    }

    private static SourcePos placeOf(Core node) {
        return node == null ? null : node.pos();
    }

    @Override
    public int hashCode() {
        int sum = kind.hashCode() + Objects.hashCode(placeOf(untoldAt));
        for (Core.Binary each : quotients) {
            sum += System.identityHashCode(each);
        }
        return sum;
    }

    @Override
    public String toString() {
        String said = kind == Kind.QUOTIENTS ? "quotients " + quotients.size() : kind.toString();
        return untoldAt == null ? said : said + ", untold at " + untoldAt.pos();
    }
}
