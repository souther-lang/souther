package souther.test;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Optional;
import java.util.function.Supplier;
import org.jacoco.agent.rt.RT;
import org.junit.platform.engine.TestExecutionResult;
import org.junit.platform.engine.support.descriptor.ClassSource;
import org.junit.platform.launcher.TestExecutionListener;
import org.junit.platform.launcher.TestIdentifier;
import org.junit.platform.launcher.TestPlan;

/**
 * What each test class covered, written out one class at a time.
 *
 * <p>A coverage agent records what a JVM ran as one growing set. Which test class ran which branch
 * is not in it, and that is the question a run under {@code -Pcoverage-by-class} asks: a class
 * whose every branch some other class also runs is a candidate for being asked whether it says
 * anything of its own. So the agent's data is taken and reset at the end of every class, and what
 * accumulated since the last reset is that class's. This holds because a fork runs its classes one
 * after another — the surefire configuration says so, and a run with classes interleaved in one JVM
 * would attribute one class's branches to the next.
 *
 * <p>Data recorded before the first class — discovery, the loading of the engines — belongs to no
 * class and is dropped when the plan starts. A nested class is written under its own name, so what
 * the outer class ran after its nested ones finished is written under the outer name; a reader
 * merges by the outermost class.
 *
 * <p>Registered through {@code META-INF/services}, so every module's tests carry it. Without
 * {@value #DIRECTORY_PROPERTY} it does nothing and touches nothing: the agent is only present when
 * the profile put it there, and a plain run must not reach for it.
 */
public final class CoverageByClass implements TestExecutionListener {

    /** Where a run wanting this writes each class's data; unset in a plain run. */
    public static final String DIRECTORY_PROPERTY = "souther.test.coverage.dir";

    private final Optional<Path> directory;
    private final Supplier<byte[]> takeAndReset;

    /** What the service loader constructs: the agent's data, into the directory the run named. */
    public CoverageByClass() {
        this(
                Optional.ofNullable(System.getProperty(DIRECTORY_PROPERTY)).map(Path::of),
                Agent::takeAndReset);
    }

    /**
     * The same over {@code takeAndReset}, which is asked for what was recorded since it was last
     * asked, and over {@code directory}; empty means the run did not ask.
     */
    CoverageByClass(Optional<Path> directory, Supplier<byte[]> takeAndReset) {
        this.directory = directory;
        this.takeAndReset = takeAndReset;
    }

    @Override
    public void testPlanExecutionStarted(TestPlan testPlan) {
        if (directory.isEmpty()) {
            return;
        }
        takeAndReset.get();
    }

    @Override
    public void executionFinished(TestIdentifier identifier, TestExecutionResult result) {
        if (directory.isEmpty()) {
            return;
        }
        Optional<String> className = identifier.getSource()
                .filter(ClassSource.class::isInstance)
                .map(ClassSource.class::cast)
                .map(ClassSource::getClassName);
        if (className.isEmpty()) {
            return;
        }
        Path dir = directory.get();
        try {
            Files.createDirectories(dir);
            Files.write(dir.resolve(className.get() + ".exec"), takeAndReset.get());
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    /**
     * The agent, reached only from a run that asked for this. Its own class so that a plain run
     * never links against the agent's runtime, which is on no plain run's classpath.
     */
    private static final class Agent {
        private Agent() {
        }

        static byte[] takeAndReset() {
            return RT.getAgent().getExecutionData(true);
        }
    }
}
