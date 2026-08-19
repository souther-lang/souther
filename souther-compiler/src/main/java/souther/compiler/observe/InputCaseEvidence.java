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
 * @param at               which of the behavior's inputs this is, counted from zero. Held rather
 *                         than left to the index of the list these arrive in: a type that says it
 *                         is the evidence of <em>one</em> input and cannot answer which one is a
 *                         value that only means something beside the list it came from, and every
 *                         reader wanting the position had to be handed it a second time. How it is
 *                         written to a person — {@code #1} for the first — is the reader's, and a
 *                         one-based number here would be this measure spelling a report's word
 * @param excluded         cases the position's own rules refuse. Declared and not coverable: the
 *                         type has them and no value of one can be constructed (E1903), so they stay
 *                         in {@link #declared} because what the type can be is part of what the model
 *                         says, and they are out of {@link #coverable} because no row can be written
 *                         at them. Nothing a body declares reaches this: what leaves a denominator
 *                         is what the rules refuse
 * @param unclassifiedRows rows whose input case could not be read
 */
public record InputCaseEvidence(int at, Set<TypeSymbol> declared, Set<TypeSymbol> specified,
                                Set<TypeSymbol> executed, Set<TypeSymbol> verified,
                                Set<TypeSymbol> excluded, int unclassifiedRows) {

    public InputCaseEvidence {
        declared = Evidence.ordered(declared);
        specified = Evidence.ordered(specified);
        executed = Evidence.ordered(executed);
        verified = Evidence.ordered(verified);
        excluded = Evidence.ordered(excluded);
    }

    /** No cases at the given input, which is what a position that is not a sum has. */
    public static InputCaseEvidence none(int at) {
        return new InputCaseEvidence(at, Set.of(), Set.of(), Set.of(), Set.of(), Set.of(), 0);
    }

    /** The cases a row can be written at: what the type declares, less what its rules refuse. */
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
