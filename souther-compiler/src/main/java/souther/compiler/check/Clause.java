package souther.compiler.check;

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
 * <p>{@code name} and {@code at} are both optional and are optional for different reasons, which is
 * what {@link #merge} turns on. An absent name is a fact about the declaration: the author wrote
 * none, and every reading of that declaration finds none. An absent {@code at} is a fact about this
 * compile: the clause was written somewhere, and whether that somewhere can be quoted depends on
 * which representation the clause was reached through.
 */
record Clause(Id id, Optional<ClauseName> name, Optional<CitableRegion> at) {

    Clause {
        Objects.requireNonNull(id, "a clause is one clause");
        Objects.requireNonNull(name, "a clause was written with a name or without one");
        Objects.requireNonNull(at, "a clause can be pointed at or it cannot");
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
     * <p>What may differ between two readings is {@code at} and only {@code at}, because only it is
     * knowledge this compile has rather than something the declaration says. Everything else
     * differing is this compiler having called two clauses one clause, or one clause two.
     */
    static Clause merge(Clause a, Clause b) {
        if (!a.id.equals(b.id)) {
            throw new NotOneClause("two clauses, " + a.id + " and " + b.id + ", merged as one");
        }
        if (!a.name.equals(b.name)) {
            throw new NotOneClause("clause " + a.id + " is named " + a.name.orElse(null)
                    + " in one reading and " + b.name.orElse(null) + " in another");
        }
        if (a.at.isPresent() && b.at.isPresent() && !a.at.equals(b.at)) {
            throw new NotOneClause("clause " + a.id + " is written at " + a.at.get().start()
                    + " in one reading and at " + b.at.get().start() + " in another");
        }
        return a.at.isPresent() ? a : b;
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
    static final class NotOneClause extends IllegalStateException {

        private static final long serialVersionUID = 1L;

        NotOneClause(String message) {
            super(message);
        }
    }
}
