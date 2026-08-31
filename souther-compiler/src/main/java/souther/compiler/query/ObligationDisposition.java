package souther.compiler.query;

import java.util.Collections;
import java.util.EnumSet;
import java.util.Set;

/**
 * Where one obligation stands in the account a report counts it in.
 *
 * <p>Derived from the evidence and never held beside it. What the readings came to
 * ({@link ObligationCoverage}) and what has shown a row can be written here
 * ({@link ItemAssessment.WritabilityEvidence}) are answers to two questions, and this is the one
 * question a count, a finding and a build's refusal all put: is this row written, owed, or neither.
 * Asked of the evidence at each of those places instead, the three had three chances to read one
 * pair of answers differently.
 *
 * <p>Four states, and three of them are counted. A counted obligation is one the model owes a row at
 * and the rows were read against, so the three make a partition of the denominator: a row stands at
 * it, no row does and the model says one can be written, or nobody can say which. What is not
 * counted is said with every reason it is not, because the reasons are independent — nothing was
 * read <em>and</em> nothing has shown a row can be written is a state, and a disposition naming one
 * of the two would be choosing between them.
 */
public sealed interface ObligationDisposition {

    /** One this account counts, which is one the rows were read against and a row could answer. */
    sealed interface Counted extends ObligationDisposition {}

    /** A row this compilation observed stands at the point. */
    record Met() implements Counted {}

    /**
     * No row is at the point, the readings ran to the end, and something has shown a row can be
     * written there. The one state a finding is made of and a build can be told to refuse over.
     */
    record Unmet() implements Counted {}

    /**
     * No row was seen and a reading that could have been holding one did not run to the end.
     *
     * <p>Counted and never a finding. Whether a row is at the point is what nobody can say, so an
     * author told to write one may be told to write one they have written; and left out of the
     * count, an obligation the rows may already answer would go unsaid.
     */
    record Undecided() implements Counted {}

    /** One this account does not count, with every reason it does not. */
    record NotCounted(Set<Reason> because) implements ObligationDisposition {

        public NotCounted {
            if (because == null || because.isEmpty()) {
                throw new IllegalArgumentException(
                        "an obligation left out of the count says why it is out");
            }
            because = Collections.unmodifiableSet(EnumSet.copyOf(because));
        }
    }

    /** Why an obligation is not counted. Both can hold of one obligation. */
    enum Reason {
        /** Nothing was read against the point, so there is nothing to have found. */
        NOTHING_WAS_READ,
        /** Nothing has shown a row can be written here, so a miss is where the reading stopped
         *  rather than where the model does. */
        NOT_KNOWN_TO_BE_WRITABLE
    }

    /**
     * Where {@code coverage} and {@code writable} put the obligation.
     *
     * <p>The one place the pair is read. A row found answers first and on its own — it is what the
     * point asked for, and it proves the point can be written at, so nothing beside it can take it
     * back. Below that the two reasons for not counting are collected together, and only a counted
     * obligation is told apart by what the readings found.
     */
    static ObligationDisposition of(ObligationCoverage coverage,
                                    ItemAssessment.WritabilityEvidence writable) {
        if (coverage.hasRowWitness()) {
            return new Met();
        }
        Set<Reason> because = EnumSet.noneOf(Reason.class);
        if (!coverage.hasAnswer()) {
            because.add(Reason.NOTHING_WAS_READ);
        }
        if (!writable.known()) {
            because.add(Reason.NOT_KNOWN_TO_BE_WRITABLE);
        }
        if (!because.isEmpty()) {
            return new NotCounted(because);
        }
        return switch (coverage) {
            case ObligationCoverage.Missed _ -> new Unmet();
            case ObligationCoverage.Undecided _ -> new Undecided();
            // Both are answered above: a witness is met, and nothing read is not counted.
            case ObligationCoverage.Witnessed _, ObligationCoverage.NotMeasured _ ->
                    throw new IllegalStateException(
                            "an obligation counted and neither missed nor undecided: " + coverage);
        };
    }
}
