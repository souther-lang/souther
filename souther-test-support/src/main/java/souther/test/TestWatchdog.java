package souther.test;

import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.function.Consumer;
import java.util.function.LongSupplier;
import org.junit.jupiter.api.extension.AfterEachCallback;
import org.junit.jupiter.api.extension.BeforeEachCallback;
import org.junit.jupiter.api.extension.ExtensionContext;

/**
 * Stops a fork whose test does not come back, and says which test it was.
 *
 * <p>No test asserts on how long it took: cost is held by counts, and a test is never wrong for
 * being slow. What a count cannot do is end code that never returns, and a JUnit timeout cannot
 * either: it interrupts the test's thread, and a loop that ignores interrupts goes on. So this runs
 * apart from the test. A daemon thread looks at every running test, and one that has run longer
 * than the limit gets its name and every thread's stack printed to stderr, after which the JVM is
 * halted. Surefire reports the fork as crashed, which is how a build that would have hung ends.
 *
 * <p>The limit is far past anything a test does on a loaded machine, so it never decides the result
 * of a test that passes. {@value #LIMIT_PROPERTY} sets it in seconds.
 *
 * <p>Registered through {@code META-INF/services} and switched on by surefire's
 * {@code junit.jupiter.extensions.autodetection.enabled}, so every module's tests carry it and no
 * test opts in. A test is running from the first callback before it to the last callback after it.
 */
public final class TestWatchdog implements BeforeEachCallback, AfterEachCallback {

    /** The limit in seconds; unset means ten minutes. */
    public static final String LIMIT_PROPERTY = "souther.test.watchdog.seconds";

    private static final Duration DEFAULT_LIMIT = Duration.ofMinutes(10);
    private static final long LOOK_EVERY_MILLIS = 1_000;
    private static final int EXIT_STATUS = 70;

    /** A test that ran past the limit, and for how long. */
    record Expired(String test, Duration ran) {
    }

    /** The tests running now, by unique id, with the reading of the clock each began at. */
    static final class Running {
        private final Map<String, Began> began = new ConcurrentHashMap<>();
        private final LongSupplier nanos;
        private final Duration limit;
        private final Consumer<Expired> onExpiry;

        /** The expiry action is what is done about a test past the limit; production halts. */
        Running(LongSupplier nanos, Duration limit, Consumer<Expired> onExpiry) {
            this.nanos = nanos;
            this.limit = limit;
            this.onExpiry = onExpiry;
        }

        void began(String uniqueId, String name) {
            began.put(uniqueId, new Began(name, nanos.getAsLong()));
        }

        void ended(String uniqueId) {
            began.remove(uniqueId);
        }

        /** Hands every test that has run longer than the limit to the expiry action. */
        void look() {
            long now = nanos.getAsLong();
            List<Expired> expired = new ArrayList<>();
            for (Began test : began.values()) {
                Duration ran = Duration.ofNanos(now - test.nanos());
                if (ran.compareTo(limit) > 0) {
                    expired.add(new Expired(test.name(), ran));
                }
            }
            expired.forEach(onExpiry);
        }

        private record Began(String name, long nanos) {
        }
    }

    /** The one watch of this JVM, started with its first test. */
    private static final class Shared {
        static final Running RUNNING = start();

        private static Running start() {
            Running running = new Running(System::nanoTime, limit(), Shared::halt);
            Thread looker = new Thread(() -> {
                while (true) {
                    try {
                        Thread.sleep(LOOK_EVERY_MILLIS);
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

        private static void halt(Expired expired) {
            System.err.println("TestWatchdog: " + expired.test() + " has run for "
                    + expired.ran().toSeconds() + "s, past the limit; halting the JVM. Stacks:");
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

    @Override
    public void beforeEach(ExtensionContext context) {
        Shared.RUNNING.began(context.getUniqueId(), context.getDisplayName() + " of "
                + context.getRequiredTestClass().getName());
    }

    @Override
    public void afterEach(ExtensionContext context) {
        Shared.RUNNING.ended(context.getUniqueId());
    }
}
