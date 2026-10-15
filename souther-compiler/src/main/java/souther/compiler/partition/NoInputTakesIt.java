package souther.compiler.partition;

import souther.compiler.inputs.EmptyInput;

import java.util.Objects;

/**
 * Why no input brings the conditions of a way out as the way took them, all at once — a proof, and
 * never that a search for one fell short.
 *
 * <p>Two kinds, because they are proved by two things. Conditions that ask a row for two cases of
 * one value, two answers of one truth or counts that leave none in common clash as conditions,
 * whatever the numbers; conditions that each leave values can still leave none together once what
 * the declarations hold is taken in with them, and that is the numbers' answer.
 */
public sealed interface NoInputTakesIt {

    /** Two conditions on the way ask for what no row is at once ({@link Reachability}). */
    record TheConditionsClash(Reachability why) implements NoInputTakesIt {

        public TheConditionsClash {
            Objects.requireNonNull(why, "conditions clash at something");
        }
    }

    /** What the declarations hold, with the numbers the conditions on the way state, leaves no
     *  input. */
    record TheNumbersLeaveNone(EmptyInput why) implements NoInputTakesIt {

        public TheNumbersLeaveNone {
            Objects.requireNonNull(why, "the numbers leave none for a reason");
        }
    }
}
