package souther.compiler.check;

import souther.compiler.core.Core;
import souther.compiler.diag.SourcePos;
import souther.compiler.types.TypeKey;
import souther.compiler.types.ValueName;

import java.util.Objects;

/**
 * An expression whose own working may end a run of a row, as a report names it: a construction
 * whose invariant is not shown to hold on every run that makes it, a call of a behavior that is
 * not shown to be got past, or something else worked out. Where a stop is left untold, this is
 * where, as the reading that left it found it; and where a behavior called is not shown to be got
 * past, this is where in its body the proof gave out.
 *
 * <p>Said once for both: what a run of a row may stop in is the same question in the body that
 * writes it and in a caller of that body, so the two are told in the same words.
 */
public sealed interface StopOrigin {

    /** Where it is written. */
    SourcePos at();

    /**
     * {@code e} as a report names it: a construction by its type, a call of a behavior with what
     * that behavior is told of ({@link BehaviorAnswers#passageOf}), and anything else by where it
     * is written.
     */
    static StopOrigin of(Core e, BehaviorAnswers answers) {
        Core written = Core.withoutStanding(e);
        if (written instanceof Core.Construct made) {
            return new AConstruction(made.pos(), made.typeName().key());
        }
        if (AnOperationApplied.of(written) instanceof AnOperationApplied applied
                && applied.operation() instanceof ValueName.Behavior called) {
            return new ACall(written.pos(), called, answers.passageOf(called));
        }
        return new SomethingWorkedOut(written.pos());
    }

    /** A construction of {@code type}, of which it is not shown that every run making it keeps
     *  its invariant. The type is held as the declaration it is, and not by its name: two modules
     *  may each declare one of a name. */
    record AConstruction(SourcePos at, TypeKey type) implements StopOrigin {

        public AConstruction {
            Objects.requireNonNull(at, "a construction is written somewhere");
            Objects.requireNonNull(type, "a construction is of some type");
        }
    }

    /**
     * A call of {@code behavior}, whose own passage is {@code passage}: what is told of a call is
     * asked of the behavior it calls, so the reason a call is left open is that behavior's.
     */
    record ACall(SourcePos at, ValueName.Behavior behavior, CallPassage passage)
            implements StopOrigin {

        public ACall {
            Objects.requireNonNull(at, "a call is written somewhere");
            Objects.requireNonNull(behavior, "a call is of some behavior");
            Objects.requireNonNull(passage, "what the behavior called is told of");
        }
    }

    /** Something else whose own working may end a run. */
    record SomethingWorkedOut(SourcePos at) implements StopOrigin {

        public SomethingWorkedOut {
            Objects.requireNonNull(at, "it is written somewhere");
        }
    }
}
