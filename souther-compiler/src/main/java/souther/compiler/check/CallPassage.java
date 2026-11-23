package souther.compiler.check;

import java.util.Objects;

/**
 * What a call of a behavior is told of the behavior's body, over whatever its own inputs may hold
 * ({@link BehaviorAnswers#passageOf}): that the run of every row is shown to get past working it
 * out, or that it is not, and what that rests on.
 *
 * <p>Not shown to get past is not shown to stop. {@link Open} says only that no proof was made,
 * and where it names an expression, that is where the proof gave out: the first the walk met whose
 * own working may end a run, and not every one there is.
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

    /** It is not shown that the run of every row gets past the body, and {@code why} is what that
     *  rests on. Not that some run does not. */
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

        /** The expression in the body the proof gave out at. */
        record MayStopAt(StopOrigin origin) implements WhyOpen {

            public MayStopAt {
                Objects.requireNonNull(origin, "it may stop somewhere");
            }
        }
    }
}
