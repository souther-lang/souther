package souther.compiler.partition;

import java.util.List;

/**
 * A construction a way goes through, and what a run getting past it states of the input: every
 * clause of the invariant of the type it builds holding of what it is handed.
 *
 * <p>Not a condition of the way. A construction is no fork — a run either gets past it or stops
 * there, and a run that stops reaches no rule — so it draws no line between rules and is none of
 * the conditions a rule is told apart or shown by. What it states is asked of a row composed for
 * the way all the same, since a row that stops at it is no row of the rule, and it is read with the
 * way's conditions where a way is proved to be taken by no input.
 *
 * @param states what getting past it states, in the words a composer of a row works from
 */
public record PassedConstruction(List<OnTheWay> states) {

    public PassedConstruction {
        states = List.copyOf(states);
    }
}
