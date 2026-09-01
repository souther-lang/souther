package souther.compiler;

import souther.compiler.query.PartitionEvidence;

/**
 * What the rows reached at a position a test has already measured.
 *
 * <p>Here rather than on {@link PartitionEvidence.AxisCoverage} because the unwrapping is a test's
 * to do. The measurement is what the type answers, and a position nobody measured has no numbers;
 * an accessor beside it that threw would be a second way in, and the caller that wanted the one
 * answer would be choosing between them.
 */
public final class WhatTheRowsReached {

    private WhatTheRowsReached() {
    }

    /**
     * The numbers at {@code axis}.
     *
     * @throws java.util.NoSuchElementException where nothing measured it, which in a test is the
     *                                          setup not having produced what the test is about
     */
    public static PartitionEvidence.AxisCoverage.Reached at(PartitionEvidence.AxisCoverage axis) {
        return axis.reached().made().orElseThrow();
    }
}
