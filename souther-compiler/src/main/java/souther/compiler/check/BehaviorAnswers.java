package souther.compiler.check;

import souther.compiler.meaning.CasesOfAnAnswer;
import souther.compiler.types.ValueName;

import java.util.Optional;

/**
 * Which case each behavior's answer is, read once off its body over its own parameters
 * ({@link CasesOfAnAnswer}) — for a reader of a call to one, which puts in what the call handed.
 *
 * <p>Empty where there is no such reading: a behavior with no body to read, or one this compilation
 * did not read the input of.
 */
@FunctionalInterface
public interface BehaviorAnswers {

    /** No behavior's answer read — for a reading that reads no call to one. */
    BehaviorAnswers NONE = behavior -> Optional.empty();

    /** Which case {@code behavior}'s answer is, where its body was read. */
    Optional<CasesOfAnAnswer> of(ValueName.Behavior behavior);
}
