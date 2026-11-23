package souther.compiler.partition;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.ValueName;

import java.util.ArrayList;
import java.util.List;
import java.util.Objects;

/**
 * What a working says it does not account for: nothing, the stops of some quotients by a value
 * and nothing else, or something no reader can name; and, beside any of these, the calls of a
 * behavior whose stop it leaves untold.
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
 * <p>A call is said for a reader to name, and accounts for nothing: what a call's behavior is told
 * of is asked of the behavior ({@link souther.compiler.check.BehaviorAnswers#passageOf}), and no
 * reader of this one asks it. So a working leaving a call is left to something else, and the
 * calls of two put together are the calls of both, whatever else either leaves.
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

    /**
     * A call of {@code behavior}, written at {@code at}, whose stop a working leaves untold: it is
     * not shown that the run of every row gets past working its body out.
     */
    record ACall(ValueName.Behavior behavior, SourcePos at) {

        ACall {
            Objects.requireNonNull(behavior, "a call is of some behavior");
            Objects.requireNonNull(at, "a call is written somewhere");
        }
    }

    static final NotAccountedFor NOTHING = new NotAccountedFor(Kind.NOTHING, List.of(),
            List.of());

    /** Something else and no call. Not handed out: what is left to something else is made from
     *  what was left before ({@link #andSomethingElse}), so that no reader widening it drops the
     *  calls it holds. */
    private static final NotAccountedFor SOMETHING_ELSE = new NotAccountedFor(
            Kind.SOMETHING_ELSE, List.of(), List.of());

    private final Kind kind;
    private final List<Core.Binary> quotients;
    private final List<ACall> calls;

    /** The quotients are a set of nodes: each once, by the node it is. The calls are a set of
     *  values, each once, in the order first met. */
    private NotAccountedFor(Kind kind, List<Core.Binary> quotients, List<ACall> calls) {
        this.kind = kind;
        List<Core.Binary> distinct = new ArrayList<>();
        for (Core.Binary each : quotients) {
            if (distinct.stream().noneMatch(one -> one == each)) {
                distinct.add(each);
            }
        }
        this.quotients = List.copyOf(distinct);
        this.calls = calls.isEmpty() ? List.of() : calls.stream().distinct().toList();
    }

    /** The stops of {@code nodes}, quotients by a value, and nothing else; something else where
     *  there are none. */
    static NotAccountedFor quotients(List<Core.Binary> nodes) {
        return nodes.isEmpty() ? SOMETHING_ELSE
                : new NotAccountedFor(Kind.QUOTIENTS, List.copyOf(nodes), List.of());
    }

    /** This, and something else beside it: what a reader leaves where it cannot name what is
     *  left, with every call this names still named. */
    NotAccountedFor andSomethingElse() {
        return join(SOMETHING_ELSE);
    }

    /** The stop of {@code call} left untold, which is something else. */
    static NotAccountedFor aCall(ACall call) {
        return new NotAccountedFor(Kind.SOMETHING_ELSE, List.of(), List.of(call));
    }

    Kind kind() {
        return kind;
    }

    /** The calls whose stop is left untold, in the order first met. */
    List<ACall> calls() {
        return calls;
    }

    /** Both put together. */
    NotAccountedFor join(NotAccountedFor other) {
        if (kind == Kind.NOTHING && calls.isEmpty()) {
            return other;
        }
        if (other.kind == Kind.NOTHING && other.calls.isEmpty()) {
            return this;
        }
        List<ACall> bothCalls = other.calls.isEmpty() ? calls
                : calls.isEmpty() ? other.calls : both(calls, other.calls);
        if (kind == Kind.SOMETHING_ELSE || other.kind == Kind.SOMETHING_ELSE) {
            return bothCalls.isEmpty() ? SOMETHING_ELSE
                    : new NotAccountedFor(Kind.SOMETHING_ELSE, List.of(), bothCalls);
        }
        List<Core.Binary> both = new ArrayList<>(quotients);
        both.addAll(other.quotients);
        return new NotAccountedFor(Kind.QUOTIENTS, both, bothCalls);
    }

    private static List<ACall> both(List<ACall> one, List<ACall> other) {
        List<ACall> out = new ArrayList<>(one);
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
                && quotients.size() == that.quotients.size()
                && quotients.stream().allMatch(that::names)
                && calls.size() == that.calls.size() && that.calls.containsAll(calls);
    }

    @Override
    public int hashCode() {
        int sum = kind.hashCode();
        for (Core.Binary each : quotients) {
            sum += System.identityHashCode(each);
        }
        for (ACall each : calls) {
            sum += each.hashCode();
        }
        return sum;
    }

    @Override
    public String toString() {
        String said = kind == Kind.QUOTIENTS ? "quotients " + quotients.size() : kind.toString();
        return calls.isEmpty() ? said : said + ", calls " + calls;
    }
}
