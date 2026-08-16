package souther.compiler.check;

import souther.compiler.diag.DiagnosticPlace;
import souther.compiler.types.TypeSymbol;

import java.util.Objects;
import java.util.Optional;

/**
 * One invariant clause, as what identifies it and what a diagnostic knows about it.
 *
 * <p>Four questions, kept apart because none of them answers another. Which clause it is, is
 * {@link Id}. What a sentence can call it, is {@code name} — a clause MAY be written without one.
 * Where a reader can be sent, is {@code at} — a clause of a published module was written somewhere
 * this compile has no source for. What was proved of it is neither of these and is
 * {@link InvariantChecker.Judgment}'s, which is why a clause is put on one of its sides rather than
 * carrying a verdict here.
 *
 * <p>{@code name} is optional and {@code at} is not. An absent name is a fact about the
 * declaration: the author wrote none, and every reading of that declaration finds none. Where the
 * clause is written is always answered — a clause of a published module is
 * {@link DiagnosticPlace.Unavailable}, which says where the code came from rather than being the
 * absence of an answer. It used to be absent, and absent is what every reader turned into silence.
 *
 * <p>{@code at} is the same for every reading of one clause, which is what {@link #merge} rests on.
 * Where a clause is written is settled where its text became positions and follows from the
 * declaration it is on, so a walk reaching it down two branches finds one answer twice.
 */
record Clause(Id id, Optional<ClauseName> name, DiagnosticPlace at) {

    Clause {
        Objects.requireNonNull(id, "a clause is one clause");
        Objects.requireNonNull(name, "a clause was written with a name or without one");
        Objects.requireNonNull(at, "a clause is written somewhere, quotable here or not");
        // As the declaration knows it, with no reader's route in it. Where the clause is written is
        // a fact about the declaration and the same for every reading of it; the name a reading
        // reached the code by is a fact about that reading. Carried, two readings of one clause are
        // two values, and `merge` stops being the same operation whichever way round it is asked.
        if (at instanceof DiagnosticPlace.Unavailable out) {
            at = new DiagnosticPlace.Unavailable(out.provenance().asDeclared());
        }
    }

    /**
     * Which clause: the declaration that wrote it, and which of that declaration's clauses it is.
     *
     * <p>Not the name, which a clause need not have, and not where it is written, which this compile
     * need not be able to quote — a set keyed on either of those puts two clauses the author wrote
     * separately under one key and reports one of them. Two spreads bringing one clause in twice
     * answer with one of these, which is what makes them one clause again.
     */
    record Id(TypeSymbol declaredOn, int ordinal) {

        Id {
            Objects.requireNonNull(declaredOn, "a clause is written on a declaration");
        }
    }

    /**
     * The two readings of one clause, together.
     *
     * <p>Commutative, associative and idempotent, so the order the readings of a construction are
     * combined in does not decide what is reported. Which is the whole of what this is for: two
     * branches of a conditional read one construction once each, and a first-wins union would let
     * the walk's order decide whether a warning points anywhere.
     *
     * <p>Two readings of one clause say the same thing about it, or the model contradicts itself.
     * Nothing here picks between them, which is what makes the three properties above hold rather
     * than being claimed: an operation that preferred one reading to another is a first-wins union
     * whichever rule it prefers by, and one that refused some disagreements while absorbing others
     * finds a contradiction or not depending on which pair was merged first.
     *
     * <p>It used to prefer the reading that could point somewhere, and there used to be a reason: a
     * reading that could not was an absent value, so which representation a clause was reached
     * through decided how much a reading knew. Where a clause is written is now settled where its
     * text became positions and is the same for every reading of it — a clause is quotable or it is
     * out of sight because of the declaration it is on, not because of the path a walk took to it,
     * and "no place at all" is not a thing a reading can produce. Measured over the whole suite: no
     * compile produces two readings of one clause that differ.
     */
    static Clause merge(Clause a, Clause b) {
        if (!a.id.equals(b.id)) {
            throw new NotOneClause("two clauses, " + a.id + " and " + b.id + ", merged as one");
        }
        if (!a.name.equals(b.name)) {
            throw new NotOneClause("clause " + a.id + " is named " + a.name.orElse(null)
                    + " in one reading and " + b.name.orElse(null) + " in another");
        }
        if (!a.at.equals(b.at)) {
            throw new NotOneClause("clause " + a.id + " is written at " + a.at
                    + " in one reading and at " + b.at + " in another");
        }
        return a;
    }

    /**
     * Two readings of one clause that do not agree about the clause.
     *
     * <p>Its own type because the check that would build one swallows what it throws. An analysis
     * that fell over leaves the run-time check standing, which is the right answer for a shape the
     * walk has no rule for; this is not that. It says the compiler's own model of a declaration
     * contradicts itself, and swallowed it comes out as a behavior with nothing to report — the same
     * thing a behavior whose invariants all discharge comes out as.
     * {@link InvariantChecker#gaveUp} refuses it for that reason.
     */
    static final class NotOneClause extends TheCheckDisagreesWithItself {

        private static final long serialVersionUID = 1L;

        NotOneClause(String message) {
            super(message);
        }
    }
}
