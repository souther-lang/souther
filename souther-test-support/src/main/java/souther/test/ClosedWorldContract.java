package souther.test;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * A test that closes a set this compiler declares and holds that nothing is missing from it.
 *
 * <p>What such a test establishes is a fact about the vocabulary: every question declared is reached
 * or written down as outside a run, every part of an evidence is asked for its handles, every source
 * the repository carries is written the way the rules say. It sweeps a corpus because that is how
 * the world is closed, and a model added to the corpus changes how long it takes without changing
 * what it claims.
 *
 * <p>Says nothing about when the test runs. A contract cheap enough to ask on every change and one
 * that takes a minute make the same claim, and which run each lands in is {@link Nightly}'s to say.
 */
@Target(ElementType.TYPE)
@Retention(RetentionPolicy.RUNTIME)
public @interface ClosedWorldContract {
}
