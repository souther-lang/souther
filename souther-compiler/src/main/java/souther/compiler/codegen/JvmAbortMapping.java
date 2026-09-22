package souther.compiler.codegen;

import souther.compiler.abort.AbortKind;
import souther.runtime.ConstraintViolation;
import souther.runtime.UnreachableReached;

/**
 * Which JVM exception class {@code souther-runtime} represents each {@link AbortKind} with.
 *
 * <p>The JVM's own answer to the question {@link AbortKind} states backend-neutrally: an
 * exhaustive, default-free switch, so a new {@link AbortKind} stops this build rather than reading
 * as an abort this backend has nothing to say about. Several kinds may answer the same class — the
 * JVM does not distinguish {@link AbortKind#INVARIANT_NOT_HELD} from
 * {@link AbortKind#DIVISION_BY_ZERO} by exception type, both being {@link ConstraintViolation} — and
 * that is a fact about how coarse this one carrier's vocabulary is, not a reason to leave an arm
 * unanswered.
 *
 * <p>Not a mapping a backend derives by re-reading {@code souther-runtime}'s source or the
 * specification: it is read here, once, and a conformance test holds actual runtime calls to it —
 * the same shape {@link souther.compiler.core.KernelContracts} keeps the abort vocabulary itself
 * from becoming a second hand-kept table.
 */
public final class JvmAbortMapping {

    private JvmAbortMapping() {}

    /** The JVM exception class {@code kind} is represented by. */
    public static Class<? extends RuntimeException> representationOf(AbortKind kind) {
        return switch (kind) {
            case INVARIANT_NOT_HELD -> ConstraintViolation.class;
            case ENSURES_NOT_HELD -> ConstraintViolation.class;
            case UNREACHABLE_REACHED -> UnreachableReached.class;
            case DIVISION_BY_ZERO -> ConstraintViolation.class;
            case ANSWER_HAS_NO_PLACE -> ConstraintViolation.class;
            case INVALID_BOUNDS -> ConstraintViolation.class;
        };
    }
}
