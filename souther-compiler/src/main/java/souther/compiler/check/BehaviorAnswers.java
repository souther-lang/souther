package souther.compiler.check;

import souther.compiler.types.ValueName;

import java.util.Optional;

/**
 * The body of each behavior, and of each recursive helper, as a call of it is read
 * ({@link CalledBody}), for a reader that reads what a call answers where the call stands, with the
 * parameters standing for what the call handed.
 *
 * <p>A recursive helper is here beside the behaviors because it is the other thing a call in an
 * analysed body is left standing for: every other helper was expanded where it was called.
 *
 * <p>Empty where there is no such body: a behavior with none to read, or one this compilation did
 * not read the input of, and a helper whose parameters declare no types.
 */
public interface BehaviorAnswers {

    /** No body of either — for a reading that reads no call to one. */
    BehaviorAnswers NONE = new BehaviorAnswers() {

        @Override
        public Optional<CalledBody> bodyOf(ValueName.Behavior behavior) {
            return Optional.empty();
        }

        @Override
        public Optional<CalledBody> bodyOf(ValueName.Helper recursion) {
            return Optional.empty();
        }
    };

    /** The body of {@code behavior} as a call of it is read, where it has one. */
    Optional<CalledBody> bodyOf(ValueName.Behavior behavior);

    /** The body of the recursive helper {@code recursion} as a call of it is read, where it has
     *  one. */
    Optional<CalledBody> bodyOf(ValueName.Helper recursion);
}
