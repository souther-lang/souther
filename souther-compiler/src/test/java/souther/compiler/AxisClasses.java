package souther.compiler;

import souther.compiler.query.PartitionEvidence;

import java.util.List;

/** What a test names an axis's classes by, where what it is asserting is the names. */
final class AxisClasses {

    private AxisClasses() {
    }

    /** The names alone, for an assertion about which classes a position has rather than about which
     *  position each of them is of. */
    static List<String> names(List<PartitionEvidence.AxisClass> classes) {
        return classes.stream().map(PartitionEvidence.AxisClass::name).toList();
    }
}
