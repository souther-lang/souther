package souther.compiler.observe;

import souther.compiler.types.TypeName;

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
 * @param unclassifiedRows rows whose input case could not be read
 */
public record InputCaseEvidence(Set<TypeName> declared, Set<TypeName> specified,
                                Set<TypeName> executed, Set<TypeName> verified,
                                int unclassifiedRows) {

    public InputCaseEvidence {
        declared = Evidence.ordered(declared);
        specified = Evidence.ordered(specified);
        executed = Evidence.ordered(executed);
        verified = Evidence.ordered(verified);
    }

    public static InputCaseEvidence none() {
        return new InputCaseEvidence(Set.of(), Set.of(), Set.of(), Set.of(), 0);
    }

    /** Cases this input can be that no row uses. */
    public List<TypeName> unspecified() {
        return Evidence.missingFrom(declared, specified);
    }

    public MeasurementStatus status() {
        return Evidence.status(declared, unclassifiedRows);
    }
}
