package souther.compiler.check;

import java.math.BigDecimal;

/**
 * The scales a Decimal operation runs at, as this compiler holds them.
 *
 * <p>A scale is an {@code Int}, which is signed 64-bit, and the scales a Decimal operation runs at
 * are the signed 32-bit numbers — the specification writes the two ends out (spec
 * §a-scale-is-used-as-the-number-written). A scale outside them answers nothing rather than
 * answering at a scale it was narrowed to, so a reading has no quotient to state a range about
 * there, for the same reason it has none where the divisor is zero.
 *
 * <p>Written here rather than read out of the run time. The specification states the range, and the
 * compiler and the run time are two implementations of that sentence: a reading that called into
 * {@code souther.runtime} would be a reading whose soundness depended on which backend was linked,
 * and what the analysis is about is the language. That is only worth saying because the range is in
 * the specification — read off the run time it would be an implementation's number, and this would
 * be a copy of it rather than a second reading of one rule. The two are held together by a test
 * over the ends (ADR-0112).
 *
 * <p>This is not the reading's budget. How far from the point a reading will lay out a grid is
 * {@link ReadingPolicy#laysOutAGridAt}, which is what a compilation is prepared to spend and not a
 * statement about which divisions run. Nor is it a claim that a division at an admitted scale has an
 * answer: a scale at the end of this range is received exactly and still names a quotient no
 * {@code Decimal} holds, which the run time reports as an abort of that operation.
 */
final class ScaleRange {

    private ScaleRange() {
    }

    /**
     * The place count {@code scale} names, or null where the run time could not be handed that
     * number as the number it is.
     */
    static Integer receivedUnchanged(BigDecimal scale) {
        try {
            return scale.intValueExact();
        } catch (ArithmeticException _) {
            return null;
        }
    }
}
