package souther.compiler.check;

import souther.compiler.diag.SourcePos;
import souther.compiler.types.ValueName;

import java.util.Objects;

/**
 * What a call of a behavior is told of the behavior's body, over whatever its own inputs may hold
 * ({@link BehaviorAnswers#passageOf}): that the run of every row is shown to get past working it
 * out, or that it is not, and what that rests on.
 *
 * <p>Not shown to get past is not shown to stop. {@link Open} says only that no proof was made,
 * and what it names is where the proof gave out: the first expression the walk met whose own
 * working may end a run, and not every one there is.
 */
public sealed interface CallPassage {

    /** The run of every row is shown to get past it. */
    CallPassage PAST = new Past();

    /** Whether the run of every row is shown to get past it. */
    default boolean getsPast() {
        return this instanceof Past;
    }

    /** The run of every row is shown to get past the body. */
    record Past() implements CallPassage {}

    /** No run of a row is shown to get past the body, for {@code why}. */
    record Open(WhyOpen why) implements CallPassage {

        public Open {
            Objects.requireNonNull(why, "a passage is left open for some reason");
        }
    }

    /** What a passage left open rests on. */
    sealed interface WhyOpen {

        /** The behavior has no body in the model to ask, one injected from outside it included. */
        record NoBody() implements WhyOpen {}

        /** Asking the body asks the behavior again, through the calls it makes: no answer is
         *  made, and no expression is named. */
        record OnACycle() implements WhyOpen {}

        /** The body is there, and what its inputs or its rules hold is not read. */
        record NotRead() implements WhyOpen {}

        /**
         * A construction written at {@code at}, of {@code type}, whose invariant is not shown to
         * hold where it is made.
         */
        record AConstruction(SourcePos at, String type) implements WhyOpen {

            public AConstruction {
                Objects.requireNonNull(at, "a construction is written somewhere");
                Objects.requireNonNull(type, "a construction is of some type");
            }
        }

        /**
         * A call written at {@code at} of {@code behavior}, whose own passage is {@code passage}:
         * what is told of a call is asked of the behavior it calls, so the reason a call is left
         * open is that behavior's.
         */
        record ACall(SourcePos at, ValueName.Behavior behavior, CallPassage passage)
                implements WhyOpen {

            public ACall {
                Objects.requireNonNull(at, "a call is written somewhere");
                Objects.requireNonNull(behavior, "a call is of some behavior");
                Objects.requireNonNull(passage, "what the behavior called is told of");
            }
        }

        /** Something else written at {@code at} whose own working may end a run. */
        record SomethingWorkedOut(SourcePos at) implements WhyOpen {

            public SomethingWorkedOut {
                Objects.requireNonNull(at, "it is written somewhere");
            }
        }
    }
}
