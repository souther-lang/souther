package souther.compiler.check;

import souther.compiler.types.ValueName;

import java.util.Optional;

/**
 * The body of each behavior as a call of it is read ({@link CalledBody}), for a reader that reads
 * what a call answers where the call stands, with the parameters standing for what the call
 * handed.
 *
 * <p>Empty where there is no such body: a behavior with none to read, or one this compilation did
 * not read the input of.
 */
@FunctionalInterface
public interface BehaviorAnswers {

    /** No behavior's body — for a reading that reads no call to one. */
    BehaviorAnswers NONE = behavior -> Optional.empty();

    /** The body of {@code behavior} as a call of it is read, where it has one. */
    Optional<CalledBody> bodyOf(ValueName.Behavior behavior);
}
