package souther.test;

import org.junit.jupiter.api.Tag;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * A test left out of the run a change waits on, and asked once a night instead.
 *
 * <p>What it costs is the whole of the reason. A test is here because paying for it on every change
 * buys less than the wait costs, which is a fact about this machine and this suite rather than about
 * what the test claims — so it is written beside the claim and not derived from it, and a test that
 * becomes cheap loses this and keeps what it says.
 *
 * <p>The tag is what surefire reads, and it is spelled here once. A plain run leaves the tag out
 * through {@code test.excluded.groups}; a run that means to ask these empties that property.
 */
@Target(ElementType.TYPE)
@Retention(RetentionPolicy.RUNTIME)
@Tag(Nightly.TAG)
public @interface Nightly {

    /** How the tag is spelled where a build names it. */
    String TAG = "nightly";
}
