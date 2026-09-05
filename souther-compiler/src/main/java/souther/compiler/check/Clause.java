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
public record Clause(Id id, Optional<ClauseName> name, DiagnosticPlace at) {

    public Clause {
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
     * The clause a walk over a declaration's invariants arrived at.
     *
     * <p>The one way to make one. Everything that names a clause — a diagnostic about what it could
     * not prove, a line a bound of it drew — is naming the same rule, and a second construction is a
     * second chance for two surfaces to call one clause by different words.
     */
    public static Clause of(TypeOps.Declared declared) {
        return new Clause(new Id(declared.declaredOn(), declared.ordinal()),
                declared.clause().name().map(ClauseName::new),
                DiagnosticPlace.of(declared.clause().reportedAt()));
    }

    /** This clause, as what identifies it and what to call it. */
    public Ref ref() {
        return new Ref(id, name);
    }

    /**
     * Which clause it is and what a report calls it, without where a reader can be sent.
     *
     * <p>Two of the four questions above, for the readers that ask only those. What names a line is
     * which clause drew it, and where a reader can be sent is a question only a diagnostic asks —
     * asked of every clause a bound was read from, a clause whose region names no source could not
     * be recorded at all, and the rule that placed the edge would go unnamed for want of an answer
     * nobody wanted.
     *
     * <p>Inside the reading of a declaration's clauses, and no further. This says which clause of
     * which declaration, which is what a walk over a declaration's invariants has to hand; a clause
     * is one of the things a rule of the model can be, and once something has been attributed to a
     * rule what carries it is {@link RuleRef}. Handed on as this, every reader downstream had to
     * work the rule back out for itself, and the ones written while only invariants arrived assumed
     * the answer.
     */
    public record Ref(Id id, Optional<ClauseName> name) {

        public Ref {
            Objects.requireNonNull(id, "a clause is one clause");
            Objects.requireNonNull(name, "a clause was written with a name or without one");
        }

        /** The clause a walk over a declaration's invariants arrived at. */
        public static Ref of(TypeOps.Declared declared) {
            return new Ref(new Id(declared.declaredOn(), declared.ordinal()),
                    declared.clause().name().map(ClauseName::new));
        }

        @Override
        public String toString() {
            return id.declaredOn().name() + "#" + id.ordinal()
                    + name.map(n -> " (" + n + ")").orElse("");
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
    public record Id(TypeSymbol.AtModule declaredOn, int ordinal) {

        public Id {
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
    public static Clause merge(Clause a, Clause b) {
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
     * <p>What a declaration says is one thing, and two readings of it are two accounts of that one
     * thing. Where they disagree about where a clause is written, one of them is about a clause the
     * other is not, and everything either says of it is filed against the wrong obligation. There is
     * no answer to compose out of the two: taking one publishes a reading the model does not decide,
     * and a body that came back with nothing to say for that reason is a body whose invariants all
     * discharge, said in the same words.
     */
    static final class NotOneClause extends IllegalStateException {

        private static final long serialVersionUID = 1L;

        NotOneClause(String message) {
            super(message);
        }
    }
}
