package souther.compiler.partition;

import souther.compiler.coverage.ControlPlace;

import java.util.List;
import java.util.Optional;

/**
 * What a row has to be for one condition of the body to come out one way where the body reaches
 * it.
 *
 * <p>Something a row is held to beside the classes it is composed for, and never one of them. What
 * the row is for is the classes; this is what it takes to get the row past a condition that
 * stopped it.
 *
 * <p>A demand and the way to the condition, and nothing about what the condition is. How the
 * demand was arrived at — a point of a comparison's border found by searching, or what an
 * operation's answer asks of the value it was asked of — is the producer's, so what composes a row
 * against these composes it against {@link RowDemand}s whichever condition stopped the row.
 *
 * @param demands  what the row has to be for the condition to come out that way: every thing it
 *                 asks, which for a point of a border is the point and for an operation's truth
 *                 may be several at once — some element meeting a predicate, and what the
 *                 predicate asks of the rest of the row beside it
 * @param reaching what the way to the condition asks of the row — and, where a demand is one a
 *                 condition makes ({@link RowDemand.OfACondition}), the condition itself, which a
 *                 composer meets the way it meets every condition on the way
 */
public record HeldOutcome(List<RowDemand> demands, Reachability.Reaching reaching) {

    public HeldOutcome {
        demands = List.copyOf(demands);
        if (demands.isEmpty()) {
            throw new IllegalArgumentException(
                    "a condition held to coming out a way asks something of the row");
        }
    }

    /**
     * What holds each condition of one behavior, asked for one condition at a time.
     *
     * <p>Asked rather than handed over whole. Working one out can be a search for a place, and the
     * conditions a generation asks about are the few a row stopped at.
     *
     * <p>By where a run through the condition is recorded and which way it is to come out, because
     * that is what a run is checked against: what got a row past a guard is the condition coming
     * out the way the guard needs, which is false as often as true — under
     * {@code Bool.not(x <= 0)} it is {@code x <= 0} failing. Where that is recorded is a place a
     * comparison or an application comes out a way, or for a truth no construct of its own
     * records, the arm a fork on it takes.
     */
    @FunctionalInterface
    public interface Of {

        /** What brings a run to {@code place}, or why nothing does. */
        Bringing at(ControlPlace place);

        /** Nothing holds any condition — what a caller with no borders to read uses. */
        Of NOTHING = _ -> new Bringing.NothingFound();
    }

    /**
     * What brings a run to one place, or why nothing does.
     *
     * <p>Two ways of nothing and they are not one. The rules leaving no value on the side a
     * comparison comes out on is the model's: no row goes that way, and none was looked for
     * because there is none. Nothing found is this compiler's: a row may well go that way, and
     * what to hold it to was not worked out.
     */
    public sealed interface Bringing {

        /** What the row has to be. */
        record Found(HeldOutcome held) implements Bringing {}

        /** The rules leave no value on the side the comparison comes out on, so nothing does. */
        record TheRulesLeaveNoValueThere() implements Bringing {}

        /** Nothing was found that does, which does not make it a place no run comes to. */
        record NothingFound() implements Bringing {}

        /** What was found, or nothing found where {@code found} is empty. */
        static Bringing of(Optional<HeldOutcome> found) {
            return found.<Bringing>map(Found::new).orElseGet(NothingFound::new);
        }
    }
}
