package souther.compiler.observe;

import souther.compiler.types.TypeSymbol;

import java.util.List;
import java.util.Set;

/**
 * What a behavior's {@code example} rows establish about the cases one of its inputs can be.
 *
 * <p>The counterpart of {@link OutputCaseEvidence}, and deliberately not the same type: the middle
 * slot claims something else. {@link #executed} means a row applied the behavior to a value of this
 * case, not that anything was seen to come back from it.
 *
 * <ul>
 *   <li>{@link #specified} — a row writes an input of this case, and it built.</li>
 *   <li>{@link #executed} — the behavior was applied to it.</li>
 *   <li>{@link #verified} — the row that did so held.</li>
 * </ul>
 *
 * <p>Covering every case of an input is the mechanised half of asking whether a behavior is total:
 * every case the input can be, tried, and a result defined for it.
 *
 * @param excluded         cases the body says it does not answer for. Declared and not coverable: the
 *                         type has them, and a row naming one would reach an {@code unreachable} and
 *                         be E1911. They stay in {@link #declared} because what the type can be is
 *                         part of what the model says, and they are out of {@link #coverable} because
 *                         no row can be written at them
 * @param unclassifiedRows rows whose input case could not be read
 */
public record InputCaseEvidence(Set<TypeSymbol> declared, Set<TypeSymbol> specified,
                                Set<TypeSymbol> executed, Set<TypeSymbol> verified,
                                Set<TypeSymbol> excluded, int unclassifiedRows) {

    public InputCaseEvidence {
        declared = Evidence.ordered(declared);
        specified = Evidence.ordered(specified);
        executed = Evidence.ordered(executed);
        verified = Evidence.ordered(verified);
        excluded = Evidence.ordered(excluded);
    }

    public static InputCaseEvidence none() {
        return new InputCaseEvidence(Set.of(), Set.of(), Set.of(), Set.of(), Set.of(), 0);
    }

    /** The cases a row can be written at: what the type declares, less what the body rules out. */
    public List<TypeSymbol> coverable() {
        return declared.stream().filter(each -> !excluded.contains(each)).toList();
    }

    /** Cases this input can be that no row uses, and that a row could have been written for. */
    public List<TypeSymbol> unspecified() {
        return Evidence.missingFrom(declared, specified).stream()
                .filter(each -> !excluded.contains(each)).toList();
    }

    public MeasurementStatus status() {
        return Evidence.status(declared, unclassifiedRows);
    }

    /** Why there are no numbers, where there are none. Derived rather than held, for the reason
     * {@link OutputCaseEvidence#reason()} gives. */
    public Reason reason() {
        return declared.isEmpty() ? Reason.NOT_A_SUM : null;
    }

    /** Why one input's cases have no numbers. */
    public enum Reason implements MeasureReason {
        /** The position is one data rather than a sum, so there is no case to cover. */
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
