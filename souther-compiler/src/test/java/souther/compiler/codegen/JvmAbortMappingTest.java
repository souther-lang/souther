package souther.compiler.codegen;

import souther.compiler.DefaultStdlib;
import souther.compiler.abort.AbortKind;
import souther.compiler.core.Kernel;
import souther.compiler.core.KernelContracts;
import souther.runtime.ConstraintFailure;
import souther.runtime.ConstraintViolation;
import souther.runtime.DecimalMath;
import souther.runtime.EnsuresFailure;
import souther.runtime.HALF_UP;
import souther.runtime.IntMath;
import souther.runtime.InvariantFailure;
import souther.runtime.Lists;
import souther.runtime.Strings;
import souther.runtime.Temporals;
import souther.runtime.UnreachableReached;

import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.function.Executable;

import java.math.BigDecimal;
import java.time.LocalDate;
import java.util.List;

import static org.junit.jupiter.api.Assertions.assertThrows;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * {@link JvmAbortMapping} is exhaustive, and {@code souther-runtime} actually raises the class it
 * names — for a kernel's own {@link AbortKind}s and not only for the reason {@code Int} overflow
 * happens to share with the rest, so an operation whose runtime forgot one kind still fails here
 * even though the kind itself has a JVM representation.
 */
class JvmAbortMappingTest {

    private static final KernelContracts KERNELS =
            KernelContracts.of(DefaultStdlib.get().kernelSignatures());

    @Test
    void everyAbortKindHasAJvmRepresentation() {
        for (AbortKind kind : AbortKind.values()) {
            Class<? extends RuntimeException> represented = JvmAbortMapping.representationOf(kind);
            assertTrue(RuntimeException.class.isAssignableFrom(represented),
                    () -> kind + " answers " + represented);
        }
    }

    /** {@code Int}'s three checked operators, each on the pair that overflows {@code long}. */
    @Test
    void intArithmeticOverflowsAsAnswerHasNoPlace() {
        assertKernelAborts(Kernel.INT_ADD, AbortKind.ANSWER_HAS_NO_PLACE,
                () -> IntMath.addExact(Long.MAX_VALUE, 1));
        assertKernelAborts(Kernel.INT_SUBTRACT, AbortKind.ANSWER_HAS_NO_PLACE,
                () -> IntMath.subtractExact(Long.MIN_VALUE, 1));
        assertKernelAborts(Kernel.INT_MULTIPLY, AbortKind.ANSWER_HAS_NO_PLACE,
                () -> IntMath.multiplyExact(Long.MAX_VALUE, 2));
    }

    /** {@code truncatingDivide} answers a zero divisor as a case; its abort is the one pair whose
     *  quotient no {@code Int} holds. */
    @Test
    void truncatingDivideAbortsOnlyWhereTheQuotientHasNoPlace() {
        assertKernelAborts(Kernel.INT_TRUNCATING_DIVIDE, AbortKind.ANSWER_HAS_NO_PLACE,
                () -> IntMath.divideExact(Long.MIN_VALUE, -1));
    }

    /** {@code floorMod} aborts on a zero divisor like {@code /} does, and never overflows. */
    @Test
    void floorModAbortsOnAZeroDivisor() {
        assertKernelAborts(Kernel.INT_FLOOR_MOD, AbortKind.DIVISION_BY_ZERO,
                () -> IntMath.floorMod(7, 0));
    }

    /** {@code Decimal}'s three checked operators, each pushed past {@code BigDecimal}'s own scale
     *  range. */
    @Test
    void decimalArithmeticOverflowsAsAnswerHasNoPlace() {
        BigDecimal huge = new BigDecimal(BigDecimal.ONE.unscaledValue(), Integer.MIN_VALUE + 1);
        assertKernelAborts(Kernel.DECIMAL_ADD, AbortKind.ANSWER_HAS_NO_PLACE,
                () -> DecimalMath.add(huge, BigDecimal.valueOf(0.1)));
        assertKernelAborts(Kernel.DECIMAL_SUBTRACT, AbortKind.ANSWER_HAS_NO_PLACE,
                () -> DecimalMath.subtract(huge, BigDecimal.valueOf(0.1)));
        assertKernelAborts(Kernel.DECIMAL_MULTIPLY, AbortKind.ANSWER_HAS_NO_PLACE,
                () -> DecimalMath.multiply(huge, huge));
    }

    /** {@code Decimal.round} and {@code Decimal.toInt} refuse a scale the run time does not take. */
    @Test
    void decimalRoundAndToIntAbortOnAScaleTheRunTimeDoesNotTake() {
        assertKernelAborts(Kernel.DECIMAL_ROUND, AbortKind.ANSWER_HAS_NO_PLACE,
                () -> DecimalMath.round(Long.MAX_VALUE, HALF_UP.INSTANCE, BigDecimal.ONE));
        assertKernelAborts(Kernel.DECIMAL_TO_INT, AbortKind.ANSWER_HAS_NO_PLACE,
                () -> DecimalMath.toInt(HALF_UP.INSTANCE,
                        new BigDecimal(BigDecimal.valueOf(Long.MAX_VALUE).unscaledValue())
                                .multiply(BigDecimal.TEN)));
    }

    /** {@code Decimal.divide} answers a zero divisor as a case; its abort is the scale the
     *  quotient has no place at. */
    @Test
    void decimalDivideAbortsOnlyWhereTheQuotientHasNoPlace() {
        assertKernelAborts(Kernel.DECIMAL_DIVIDE, AbortKind.ANSWER_HAS_NO_PLACE,
                () -> DecimalMath.divide(BigDecimal.ONE, BigDecimal.valueOf(3), Long.MAX_VALUE,
                        HALF_UP.INSTANCE));
    }

    /** {@code repeat}, {@code padLeft} and {@code padRight}: a count or a width no {@code String}
     *  could hold, the same law {@code Int} overflow answers to. */
    @Test
    void stringRepeatAndPaddingAbortWhereTheResultHasNoPlace() {
        assertKernelAborts(Kernel.STRING_REPEAT, AbortKind.ANSWER_HAS_NO_PLACE,
                () -> Strings.repeat("x", Integer.MAX_VALUE + 2L));
        assertKernelAborts(Kernel.STRING_PAD_LEFT, AbortKind.ANSWER_HAS_NO_PLACE,
                () -> Strings.padLeft("x", Integer.MAX_VALUE + 2L, "y"));
        assertKernelAborts(Kernel.STRING_PAD_RIGHT, AbortKind.ANSWER_HAS_NO_PLACE,
                () -> Strings.padRight("x", Integer.MAX_VALUE + 2L, "y"));
    }

    /** {@code String.slice}'s bounds may name nothing to slice at all — a different reason than an
     *  answer with no place. */
    @Test
    void stringSliceAbortsOnInvalidBounds() {
        assertKernelAborts(Kernel.STRING_SLICE, AbortKind.INVALID_BOUNDS,
                () -> Strings.slice("abc", 0, 9));
        assertKernelAborts(Kernel.STRING_SLICE, AbortKind.INVALID_BOUNDS,
                () -> Strings.slice("abc", 2, 0));
    }

    /** {@code List.rangeInclusive}'s span longer than a {@code List} can hold — the same law an
     *  {@code Int} overflow answers to (spec §stdlib-list). */
    @Test
    void listRangeInclusiveAbortsWhereTheSpanHasNoPlace() {
        assertKernelAborts(Kernel.LIST_RANGE_INCLUSIVE, AbortKind.ANSWER_HAS_NO_PLACE,
                () -> Lists.rangeInclusive(0, Long.MAX_VALUE));
    }

    /** {@code List.sum} and {@code List.product} reach {@code Int} overflow through their {@code
     *  Int} instantiation — a fact the kernel signature does not distinguish by element type. */
    @Test
    void listSumAndProductOverflowThroughTheirIntInstantiation() {
        assertKernelAborts(Kernel.LIST_SUM, AbortKind.ANSWER_HAS_NO_PLACE,
                () -> Lists.sumInt(List.of(Long.MAX_VALUE, 1L)));
        assertKernelAborts(Kernel.LIST_PRODUCT, AbortKind.ANSWER_HAS_NO_PLACE,
                () -> Lists.productInt(List.of(Long.MAX_VALUE, 2L)));
    }

    /** Every calendar shift, run off the end of what its temporal holds. */
    @Test
    void everyCalendarShiftAbortsWhereTheResultHasNoPlace() {
        LocalDate late = LocalDate.of(999999999, 12, 31);
        assertKernelAborts(Kernel.DATE_ADD_DAYS, AbortKind.ANSWER_HAS_NO_PLACE,
                () -> Temporals.addDays(late, Long.MAX_VALUE));
        assertKernelAborts(Kernel.DATE_ADD_MONTHS, AbortKind.ANSWER_HAS_NO_PLACE,
                () -> Temporals.addMonths(late, Long.MAX_VALUE));
        assertKernelAborts(Kernel.DATE_ADD_YEARS, AbortKind.ANSWER_HAS_NO_PLACE,
                () -> Temporals.addYears(late, Long.MAX_VALUE));
    }

    @Test
    void unreachableAbortsAsTheClassJvmAbortMappingNames() {
        assertThrows(JvmAbortMapping.representationOf(AbortKind.UNREACHABLE_REACHED),
                () -> UnreachableReached.reached("never"));
    }

    /**
     * {@code InvariantFailure} is what {@code __construct} answers on its failure side (spec
     * §invariant-mvp), and {@code ConstraintViolation.notHeld} is the one place any
     * {@link ConstraintFailure} leaves as an abort ({@code BodyGen}'s
     * {@code ConstraintViolation.orThrow} calls it for a construction; this calls it directly for
     * the same reason the kernel assertions above call {@code souther-runtime} directly, rather than
     * compiling and running a Souther program to reach the one line that does).
     */
    @Test
    void invariantNotHeldAbortsAsTheClassJvmAbortMappingNames() {
        InvariantFailure failure = InvariantFailure.unnamed("demo", "Positive");

        assertThrows(JvmAbortMapping.representationOf(AbortKind.INVARIANT_NOT_HELD),
                () -> { throw ConstraintViolation.notHeld(failure); });
    }

    /**
     * {@code EnsuresFailure} is what the check {@code EnsuresGen} emits at
     * {@link souther.compiler.core.EnsuresEnforcement.AtTheCallee} and
     * {@link souther.compiler.core.EnsuresEnforcement.AtEachCrossing} builds and throws through the
     * same {@code ConstraintViolation.notHeld}.
     */
    @Test
    void ensuresNotHeldAbortsAsTheClassJvmAbortMappingNames() {
        EnsuresFailure failure = new EnsuresFailure("demo", "halve", null, null, null);

        assertThrows(JvmAbortMapping.representationOf(AbortKind.ENSURES_NOT_HELD),
                () -> { throw ConstraintViolation.notHeld(failure); });
    }

    /**
     * Calls {@code raises}, checks it aborts with the class {@link JvmAbortMapping} names for
     * {@code kind}, and checks {@code kernel}'s own {@link KernelContracts} answer actually names
     * {@code kind} — so a kernel whose contract forgot the reason this call demonstrates fails here
     * rather than only in the runtime.
     */
    private static void assertKernelAborts(Kernel kernel, AbortKind kind, Executable raises) {
        assertTrue(KERNELS.contractOf(kernel).aborts().contains(kind),
                () -> kernel + "'s contract does not name " + kind
                        + ", which souther-runtime demonstrably raises");
        Class<? extends RuntimeException> expected = JvmAbortMapping.representationOf(kind);
        RuntimeException thrown = assertThrows(expected, raises,
                () -> kernel + " was expected to abort with " + kind + " (" + expected + ")");
        // ConstraintViolation carries several AbortKind at the JVM, so its own type says nothing
        // about which one; UnreachableReached is exclusive to UNREACHABLE_REACHED, so it is.
        if (expected == UnreachableReached.class) {
            assertTrue(thrown instanceof UnreachableReached);
        } else {
            assertTrue(thrown instanceof ConstraintViolation);
        }
    }
}
