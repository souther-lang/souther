package souther.compiler.observe;

import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.Set;

/**
 * What a behavior's {@code example} rows establish about the cases it can answer with.
 *
 * <p>Three sets rather than one, because how far a row got decides what it proves.
 *
 * <ul>
 *   <li>{@link #specified} — a row expects this case. Somebody wrote down that the model owes it.</li>
 *   <li>{@link #observed} — the behavior was seen to answer with this case. A row that expected
 *       something else still saw what it saw: expecting {@code Approved} and getting {@code Rejected}
 *       is no evidence for {@code Approved} and is evidence that {@code Rejected} can happen.</li>
 *   <li>{@link #verified} — a row expected this case and the behavior produced it.</li>
 * </ul>
 *
 * <p>A behavior with no {@code let} can reach {@link #specified} and no further, which is the honest
 * account of a model that has been described and not yet written.
 *
 * @param unclassifiedRows rows whose case could not be read. While this is above zero a missing case
 *                         is undecided rather than missing, because one of those rows may cover it.
 */
public record OutputCaseEvidence(Set<TypeSymbol> declared, Set<TypeSymbol> specified,
                                 Set<TypeSymbol> observed, Set<TypeSymbol> verified,
                                 int unclassifiedRows) {

    public OutputCaseEvidence {
        declared = Evidence.ordered(declared);
        specified = Evidence.ordered(specified);
        observed = Evidence.ordered(observed);
        verified = Evidence.ordered(verified);
    }

    public static OutputCaseEvidence none() {
        return new OutputCaseEvidence(Set.of(), Set.of(), Set.of(), Set.of(), 0);
    }

    /** Cases the behavior can answer with that no row expects. */
    public List<TypeSymbol> unspecified() {
        return Evidence.missingFrom(declared, specified);
    }

    /** Cases no row has confirmed the behavior answers with. */
    public List<TypeSymbol> unverified() {
        return Evidence.missingFrom(declared, verified);
    }

    public MeasurementStatus status() {
        return Evidence.status(declared, unclassifiedRows);
    }

    /** Why there are no numbers, where there are none. Derived rather than held: what makes this
     * measure unavailable is that {@link #declared} is empty, so a field beside it would be a second
     * copy of a fact this record already carries and a second thing to keep true. */
    public Reason reason() {
        return declared.isEmpty() ? Reason.NOT_A_SUM : null;
    }

    /** Why a behavior's output cases have no numbers. */
    public enum Reason implements MeasureReason {
        /** The output is one data rather than a sum, so there is no case to cover and no row can
         *  fail to cover it. */
        NOT_A_SUM(MeasurementStatus.NOT_APPLICABLE);

        private final MeasurementStatus status;

        Reason(MeasurementStatus status) {
            this.status = status;
        }

        @Override
        public MeasurementStatus status() {
            return status;
        }
    }
}
