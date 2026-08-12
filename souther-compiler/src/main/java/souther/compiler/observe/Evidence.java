package souther.compiler.observe;

import souther.compiler.types.TypeName;

import java.util.LinkedHashSet;
import java.util.List;
import java.util.Set;

/** What {@link OutputCaseEvidence} and {@link InputCaseEvidence} share: how a set of cases is held,
 * and when a gap in one may be reported as a gap. The two are separate types because what their
 * middle slot claims is different, and nothing should be able to pass one for the other. */
final class Evidence {

    static Set<TypeName> ordered(Set<TypeName> of) {
        return of == null ? Set.of()
                : java.util.Collections.unmodifiableSet(new LinkedHashSet<>(of));
    }

    static List<TypeName> missingFrom(Set<TypeName> declared, Set<TypeName> covered) {
        return declared.stream().filter(c -> !covered.contains(c)).toList();
    }

    static MeasurementStatus status(Set<TypeName> declared, int unclassifiedRows) {
        if (declared.isEmpty()) {
            // Not a sum. No row could give this position a case to cover, so the measure does not
            // apply rather than going unmade.
            return MeasurementStatus.NOT_APPLICABLE;
        }
        return unclassifiedRows == 0 ? MeasurementStatus.COMPLETE : MeasurementStatus.PARTIAL;
    }

    private Evidence() {}
}
