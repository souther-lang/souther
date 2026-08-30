package souther.compiler.check;

import souther.compiler.numeric.OrderedIntervals;
import souther.compiler.values.Emptiness;
import souther.compiler.values.Realized;
import souther.compiler.values.UnreadReason;

import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * What settling the met-together reading came to: the values, and the fate of every branch.
 *
 * <p>One computation and two projections of its result. Working {@link StatedTogether} out under an
 * allowance is what decides which values every position admits, and the same work is the only thing
 * that can say whether anybody can be in a branch of a choice — so both come back from it together,
 * as a value, and nothing recomputes either. The account of what each rule took in
 * ({@link StatedByClauses.Reading#accountOf}) consumes the fates; it holds no machinery to decide
 * one.
 *
 * <p><b>A fate is an aggregate over every place distribution put the branch, not an attribute of
 * one place.</b> The same written choice stands inside each branch of every choice met with it, and
 * one copy's branch can admit something where another copy's admits nothing — a branch of {@code B}
 * inside the left of {@code A} is refined by {@code A}'s left, and the same branch inside the right
 * by {@code A}'s right. What the written branch's author can act on is the whole declaration's
 * answer: nobody can be in it only if nobody can be in it anywhere it stands. So the sides join over
 * occurrences by {@link Emptiness#joined}, which is associative, commutative and idempotent — the
 * order the copies are met in, and how the conjunctions were bracketed, cannot reach the answer.
 *
 * @param made     the whole reading worked out, with what could not be built beside it
 * @param ordered  where every position stops, settled by the same work
 * @param outcomes the fate of both branches of every written choice, by its id
 */
record Settlement(Realized<FactSubject> made, OrderedIntervals<FactSubject> ordered,
                  Map<ChoiceId, OfAChoice> outcomes) {

    /** Both branches of one written choice, each aggregated over its occurrences. */
    record OfAChoice(Sided left, Sided right) {

        /** This choice with one more occurrence of it taken in, side by side. */
        OfAChoice alsoSeen(OfAChoice occurrence) {
            return new OfAChoice(left.alsoSeen(occurrence.left()),
                    right.alsoSeen(occurrence.right()));
        }
    }

    /**
     * One branch's fate, over every occurrence taken in so far.
     *
     * <p>{@code standing} and {@code unbuilt} carry what probing the occurrences could not build,
     * for the one case the account needs it: a branch kept without being shown live is kept with
     * the reason nobody knows, or the account would call a position open where the truth is that
     * nothing looked. Read only where the aggregate stays {@link Emptiness#UNDECIDED}; a branch
     * shown live somewhere needs no excuse, and a branch dead everywhere takes its reasons with it.
     */
    record Sided(Emptiness emptiness, Map<FactSubject, List<UnreadReason>> standing,
                 Set<FactSubject> unbuilt) {

        /** A branch nobody has probed yet, which everything joins onto. */
        static Sided settledAs(Emptiness emptiness) {
            return new Sided(emptiness, Map.of(), Set.of());
        }

        /** The same branch with one more occurrence of it taken in. */
        Sided alsoSeen(Sided other) {
            Set<FactSubject> gaveUp = new java.util.LinkedHashSet<>(unbuilt);
            gaveUp.addAll(other.unbuilt());
            return new Sided(emptiness.joined(other.emptiness()),
                    ReadByClauses.alsoSaying(standing, other.standing()), gaveUp);
        }
    }
}
