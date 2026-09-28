package souther.test;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * A test that holds what this compiler answers against an answer written down in the repository.
 *
 * <p>It claims nothing about the answer being a good one. What it records is what the answer is, so
 * that a change moving it has to move the checked-in document in the same commit and show the
 * difference to whoever reads the diff.
 *
 * <p>Says nothing about when the test runs. The diff is the whole mechanism, so deferring one of
 * these to a run nobody is waiting on would leave the document to be rewritten by somebody who did
 * not make the change — but that is a reason to leave {@link Nightly} off, not something this
 * annotation decides.
 */
@Target(ElementType.TYPE)
@Retention(RetentionPolicy.RUNTIME)
public @interface CheckedInObservation {
}
