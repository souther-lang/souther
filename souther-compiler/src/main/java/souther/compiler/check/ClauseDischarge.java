package souther.compiler.check;

import souther.compiler.diag.SourcePos;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.function.Supplier;

/**
 * How much of one clause of the model the check reads: a data's {@code invariant} (spec
 * §invariant-discharge-capability) or a behavior's {@code ensures} (spec
 * §ensures-discharge-capability).
 *
 * <p>Once some clauses are statically dischargeable and others are not, the same {@code invariant}
 * keyword means two different things to a reader: one shape reports an unguarded construction and the
 * other stays silent. Left implicit, an author believes a static guarantee exists where it does not.
 * This is the answer, per clause, so the classification is a property of the language and not of
 * whatever the checker happens to manage.
 *
 * <p>One record for both kinds because it is one question — whether what is written is a relation the
 * numeric domain reasons over, a term the check can name, or neither. What follows from the answer is
 * the reader's: for an invariant it says what discharges a construction, for a rule how much of the
 * relation there is to read. Answering it twice would be two classifications to keep agreeing.
 *
 * <p>It is the clause's own capability, read with what it names assumed to stand for itself. A
 * construction that names nothing the check can name discharges nothing whatever its clauses say —
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

    /**
     * Every reading one clause got, from what the check found of it — one where it is read one way,
     * and more where it is read more than one way.
     *
     * <p>What is written as one thing need not be read as one thing. A clause naming a helper is one
     * thing to its author and is whatever that helper states to the check, and the parts of it can be
     * read differently: a bound and a term that can only be compared for identity are discharged by
     * different guards, and something being one says nothing about whether the rest is. Answering
     * with one of them is choosing which part of a clause to describe — and if the choice is "the
     * strongest", what an author is shown is the part that will not surprise them.
     *
     * <p>{@code unread} is the part of it the check made nothing of, which is said even where the
     * rest was read. Left out, a clause half of which is outside the fragment would be described
     * entirely by the half inside it: an author reading "a guard discharges this" would write one and
     * find the construction still refused.
     *
     * <p>Written here as what it is — a function of what was found — so that it can be held to for
     * shapes a program does not take today. Every reader of a clause reaches this, and the day the
     * check reads further into what a clause names is the day a clause states two of these at once.
     *
     * @param why what the check could not read, asked for only where there is something to say
     */
    public static List<ClauseDischarge> readings(boolean asABound, boolean asATerm, boolean unread,
                                                 SourcePos clause, Supplier<String> why) {
        List<ClauseDischarge> found = new ArrayList<>();
        if (asABound) {
            found.add(derivable(clause));
        }
        if (asATerm) {
            found.add(exactMatch(clause));
        }
        // A clause nothing was found of is one nothing can be asked of, which is the same answer as a
        // clause the check read no part of.
        if (unread || found.isEmpty()) {
            found.add(runtimeOnly(clause, why.get()));
        }
        return List.copyOf(found);
    }

    /** Whether a construction of this type can be judged safe from this clause at all. */
    public boolean statically() {
        return kind != Kind.RUNTIME_ONLY;
    }
}
