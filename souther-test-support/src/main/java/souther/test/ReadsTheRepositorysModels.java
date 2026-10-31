package souther.test;

import org.junit.jupiter.api.Tag;

import java.lang.annotation.ElementType;
import java.lang.annotation.Retention;
import java.lang.annotation.RetentionPolicy;
import java.lang.annotation.Target;

/**
 * A test that reads the models this repository carries, asked where every other one of them is.
 *
 * <p>Reading them costs compiling them, which is done once for a JVM and shared by every class in it
 * ({@code RepositoryModels}). A run hands classes to its forks one at a time, so readers handed to
 * several forks compile the models once in each. The tag is what lets a run ask them together, in
 * one fork, by naming it; the tests that read the models are deferred to the nightly run
 * ({@link Nightly}), so no runner a change waits on reads them.
 *
 * <p>Said by what the test reaches and not chosen. A test that reaches the models carries this, and
 * no other does — {@code EveryTestThatSweepsACorpusSaysWhatItClaimsTest} asks both — so it says
 * nothing about what the test claims of them, which is the other annotation such a test carries.
 *
 * <p>At the top of a file, as {@link Nightly} is: a tag at a class covers the {@code @Nested}
 * classes in it.
 */
@Target(ElementType.TYPE)
@Retention(RetentionPolicy.RUNTIME)
@Tag(ReadsTheRepositorysModels.TAG)
public @interface ReadsTheRepositorysModels {

    /** How the tag is spelled where a build names it. */
    String TAG = "repository-models";
}
