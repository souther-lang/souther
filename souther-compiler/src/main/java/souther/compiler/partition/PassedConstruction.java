package souther.compiler.partition;

import souther.compiler.check.Clause;
import souther.compiler.diag.SourcePos;

import java.util.List;

/**
 * One clause of a construction a way goes through, and what a run getting past that clause states
 * of the input: the clause holding of what the construction hands it.
 *
 * <p>Not a condition of the way. A construction is no fork — a run either gets past it or stops
 * there, and a run that stops reaches no rule — so it draws no line between rules and is none of
 * the conditions a rule is told apart or shown by. What it states is asked of a row composed for
 * the way all the same, since a row that stops at it is no row of the rule, and it is read with the
 * way's conditions where a way is proved to be taken by no input.
 *
 * <p>A clause apiece rather than the construction whole. A run stops at a construction at the
 * first clause what it hands breaks, so a proof that no input takes a way, had without each clause
 * it does not need, keeps exactly the clauses the way's inputs break — and those are the ones a
 * reader is sent to where every run along the way stops ({@link DecisionReading.EveryRunStops}).
 * The clauses of one construction a way goes through are each one of these, beside each other.
 *
 * @param states what getting past the clause states, in the words a composer of a row works from
 * @param at     where the construction is written, or null where the code it stands in was made
 *               with no place
 * @param clause the clause of the invariant it is held to, or null where a declaration whose
 *               clauses govern the value was not reached, and what it states is that the invariant
 *               was not read
 */
public record PassedConstruction(List<OnTheWay> states, SourcePos at, Clause.Ref clause) {

    public PassedConstruction {
        states = List.copyOf(states);
    }
}
