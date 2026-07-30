package souther.compiler.check;

import souther.compiler.diag.SourcePos;

import java.util.Optional;

/**
 * How one clause of an invariant can be discharged at compile time (spec
 * §invariant-discharge-capability).
 *
 * <p>Once some clauses are statically dischargeable and others are not, the same {@code invariant}
 * keyword means two different things to a reader: one shape reports an unguarded construction and the
 * other stays silent. Left implicit, an author believes a static guarantee exists where it does not.
 * This is the answer, per clause, so the classification is a property of the language and not of
 * whatever the checker happens to manage.
 *
 * <p>It is the clause's own capability, read with the construction assumed to name what it is given.
 * A construction that names nothing the check can name discharges nothing whatever its clauses say —
 * that is a fact about the construction, and belongs where the construction is.
 */
public record ClauseDischarge(SourcePos clause, Kind kind, Optional<String> reason,
                             Optional<String> name) {

    /** A classification not yet attributed to a declared clause: the capability is read off the
     * expression, and the name is attached where the declaration is. */
    public ClauseDischarge(SourcePos clause, Kind kind, Optional<String> reason) {
        this(clause, kind, reason, Optional.empty());
    }

    /** The same classification under the name the clause was declared with, which is what an attempt's
     * departure arm and a boundary issue call it. */
    public ClauseDischarge named(Optional<String> declared) {
        return new ClauseDischarge(clause, kind, reason, declared);
    }

    /** What can discharge a clause. The first two are the statically dischargeable ones, and they are
     * separate because they admit different guards: a relation the domain reasons over is discharged
     * by any guard that <em>implies</em> it, while a term it can only compare for identity is
     * discharged by a guard stating the same thing and by nothing weaker. */
    public enum Kind {

        /** A relation the numeric domain reasons over: bounds, differences, sums of them. */
        DERIVABLE,

        /** A term the check can name but not reason about, discharged by a guard establishing the
         * same canonical property. */
        EXACT_MATCH,

        /** Not representable as a static obligation. No guard discharges it; the run-time check on
         * construction is the whole of its enforcement. */
        RUNTIME_ONLY
    }

    public static ClauseDischarge derivable(SourcePos clause) {
        return new ClauseDischarge(clause, Kind.DERIVABLE, Optional.empty());
    }

    public static ClauseDischarge exactMatch(SourcePos clause) {
        return new ClauseDischarge(clause, Kind.EXACT_MATCH, Optional.empty());
    }

    /** {@code reason} names what in the clause the check cannot read — there is more than one way to
     * be outside the fragment, and which one it is decides what the author can do about it. */
    public static ClauseDischarge runtimeOnly(SourcePos clause, String reason) {
        return new ClauseDischarge(clause, Kind.RUNTIME_ONLY, Optional.of(reason));
    }

    /** Whether a construction of this type can be judged safe from this clause at all. */
    public boolean statically() {
        return kind != Kind.RUNTIME_ONLY;
    }
}
