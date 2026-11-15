package souther.test;

import java.time.Duration;
import java.util.ArrayList;
import java.util.Comparator;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;
import java.util.function.Consumer;
import java.util.function.LongSupplier;
import org.junit.platform.engine.TestExecutionResult;
import org.junit.platform.launcher.TestExecutionListener;
import org.junit.platform.launcher.TestIdentifier;

/**
 * Stops a fork whose tests stop making progress, and says where.
 *
 * <p>No test asserts on how long it took: cost is held by counts, and a test is never wrong for
 * being slow. What a count cannot do is end code that never returns, and a JUnit timeout cannot
 * either: it interrupts the test's thread, and a loop that ignores interrupts goes on. So this runs
 * apart from the test. A daemon thread looks at everything JUnit is executing, and when something
 * has shown no activity for longer than the limit, the names of what is stuck and every thread's
 * stack are printed to stderr and the JVM is halted. Surefire reports the fork as crashed, which is
 * how a build that would have hung ends.
 *
 * <p>What is executing is what the JUnit Platform says is: every container and every test it
 * announces through {@code executionStarted} and {@code executionFinished}, whatever the engine
 * made it from. A class, a method, a dynamic test, a template's invocation, and the work of
 * {@code @BeforeAll}, {@code @AfterAll} and a factory's stream, which belong to the class or the
 * factory, are all inside one of those. A descriptor's activity is its own start, or the start or
 * finish of anything beneath it. A test is therefore aged from its start; a class that is running
 * many tests is never stuck while they come and go, and one whose {@code @BeforeAll} does not
 * return is.
 *
 * <p>The limit is far past anything a test does on a loaded machine, so it never decides the result
 * of a test that passes. {@value #LIMIT_PROPERTY} sets it in seconds.
 *
 * <p>Registered through {@code META-INF/services}, so the launcher finds it in every module's tests
 * and no test opts in. A hang in discovery is watched by {@link TestDiscoveryWatchdog}.
 */
public final class TestWatchdog implements TestExecutionListener {

    /** The limit in seconds; unset means ten minutes. */
    public static final String LIMIT_PROPERTY = "souther.test.watchdog.seconds";

    private static final Duration DEFAULT_LIMIT = Duration.ofMinutes(10);
    private static final Duration LONGEST_LOOK_INTERVAL = Duration.ofSeconds(1);
    private static final int EXIT_STATUS = 70;

    /** Something that showed no activity for longer than the limit, and for how long. */
    record Expired(String name, Duration idle) {
    }

    /** What is executing now, each with the reading of the clock at its latest activity. */
    static final class Running {
        private final Map<String, Watched> watched = new ConcurrentHashMap<>();
        private final LongSupplier nanos;
        private final Duration limit;
        private final Consumer<List<Expired>> onExpiry;

        /**
         * The expiry action is what is done about what is past the limit, deepest first;
         * production halts.
         */
        Running(LongSupplier nanos, Duration limit, Consumer<List<Expired>> onExpiry) {
            this.nanos = nanos;
            this.limit = limit;
            this.onExpiry = onExpiry;
        }

        /** Starts watching {@code id}, which counts as activity of everything above it. */
        void started(String id, Optional<String> parentId, String name) {
            long now = nanos.getAsLong();
            int depth = parentId.map(parent -> {
                Watched above = watched.get(parent);
                return above == null ? 1 : above.depth + 1;
            }).orElse(0);
            watched.put(id, new Watched(name, parentId, depth, now));
            touchAbove(parentId, now);
        }

        /** Stops watching {@code id}; its finish is activity of everything above it. */
        void finished(String id) {
            Watched gone = watched.remove(id);
            if (gone != null) {
                touchAbove(gone.parent, nanos.getAsLong());
            }
        }

        /** Something beneath {@code parentId} happened without being watched itself. */
        void activityBeneath(Optional<String> parentId) {
            touchAbove(parentId, nanos.getAsLong());
        }

        private void touchAbove(Optional<String> parentId, long now) {
            Optional<String> next = parentId;
            while (next.isPresent()) {
                Watched above = watched.get(next.get());
                if (above == null) {
                    return;
                }
                above.lastActivity.set(now);
                next = above.parent;
            }
        }

        /** The names of everything being watched. */
        List<String> names() {
            return watched.values().stream().map(Watched::name).toList();
        }

        /** Hands everything past the limit, deepest first, to the expiry action. */
        void look() {
            long now = nanos.getAsLong();
            List<Watched> stuck = new ArrayList<>();
            List<Expired> expired = new ArrayList<>();
            for (Watched candidate : watched.values()) {
                Duration idle = Duration.ofNanos(now - candidate.lastActivity.get());
                if (idle.compareTo(limit) > 0) {
                    stuck.add(candidate);
                }
            }
            stuck.sort(Comparator.comparingInt((Watched w) -> w.depth).reversed());
            for (Watched candidate : stuck) {
                expired.add(new Expired(candidate.name,
                        Duration.ofNanos(now - candidate.lastActivity.get())));
            }
            if (!expired.isEmpty()) {
                onExpiry.accept(expired);
            }
        }

        private record Watched(String name, Optional<String> parent, int depth,
                AtomicLong lastActivity) {
            Watched(String name, Optional<String> parent, int depth, long began) {
                this(name, parent, depth, new AtomicLong(began));
            }
        }
    }

    /** The one watch of this JVM, started with its first use. */
    private static final class Shared {
        static final Running RUNNING = start();

        private static Running start() {
            Duration limit = limit();
            Duration lookEvery = limit.dividedBy(4).compareTo(LONGEST_LOOK_INTERVAL) < 0
                    ? limit.dividedBy(4) : LONGEST_LOOK_INTERVAL;
            Running running = new Running(System::nanoTime, limit, Shared::halt);
            Thread looker = new Thread(() -> {
                while (true) {
                    try {
                        Thread.sleep(lookEvery);
                    } catch (InterruptedException e) {
                        return;
                    }
                    running.look();
                }
            }, "souther-test-watchdog");
            looker.setDaemon(true);
            looker.start();
            return running;
        }

        private static Duration limit() {
            String seconds = System.getProperty(LIMIT_PROPERTY);
            return seconds == null ? DEFAULT_LIMIT : Duration.ofSeconds(Long.parseLong(seconds));
        }

        private static void halt(List<Expired> expired) {
            System.err.println("TestWatchdog: no activity past the limit; halting the JVM. Stuck,"
                    + " deepest first:");
            for (Expired stuck : expired) {
                System.err.println("  " + stuck.name() + " idle for " + stuck.idle().toSeconds() + "s");
            }
            System.err.println("Stacks:");
            for (Map.Entry<Thread, StackTraceElement[]> thread : Thread.getAllStackTraces().entrySet()) {
                System.err.println("thread " + thread.getKey().getName() + " "
                        + thread.getKey().getState());
                for (StackTraceElement frame : thread.getValue()) {
                    System.err.println("\tat " + frame);
                }
            }
            System.err.flush();
            Runtime.getRuntime().halt(EXIT_STATUS);
        }
    }

    /** The watch every listener and the discovery watch share. */
    static Running running() {
        return Shared.RUNNING;
    }

    /** The names of what is being watched now; a test finds itself among them in a real run. */
    static List<String> runningNow() {
        return running().names();
    }

    @Override
    public void executionStarted(TestIdentifier identifier) {
        running().started(identifier.getUniqueId(), identifier.getParentId(),
                identifier.getDisplayName() + " [" + identifier.getUniqueId() + "]");
    }

    @Override
    public void executionSkipped(TestIdentifier identifier, String reason) {
        running().activityBeneath(identifier.getParentId());
    }

    @Override
    public void executionFinished(TestIdentifier identifier, TestExecutionResult result) {
        running().finished(identifier.getUniqueId());
    }
}
