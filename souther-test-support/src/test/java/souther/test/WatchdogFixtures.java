package souther.test;

import java.util.concurrent.atomic.AtomicLong;
import java.util.stream.IntStream;
import java.util.stream.Stream;
import org.junit.jupiter.api.AfterAll;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.DynamicTest;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.api.TestFactory;
import org.junit.jupiter.api.condition.EnabledIfSystemProperty;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

/**
 * Tests that do not come back, one for each place JUnit runs code, and one that is long and
 * well-behaved. They are the subject of {@code TheWatchdogStopsWhatDoesNotComeBackTest}, which runs
 * each in a JVM of its own; {@value #ENABLED_PROPERTY} is set only for that JVM, so in an ordinary
 * run every class here is skipped.
 */
final class WatchdogFixtures {

    /** Set in the child JVM that runs a fixture. */
    static final String ENABLED_PROPERTY = "souther.test.watchdog.fixture";

    private WatchdogFixtures() {
    }

    /** What a test that ignores interrupts does. */
    static final class Spin {
        private static final AtomicLong TURNS = new AtomicLong();

        private Spin() {
        }

        static void forever() {
            while (true) {
                TURNS.incrementAndGet();
            }
        }

        static void foreverIfAsked() {
            if (Boolean.getBoolean(ENABLED_PROPERTY)) {
                forever();
            }
        }
    }

    @EnabledIfSystemProperty(named = ENABLED_PROPERTY, matches = "true")
    static final class HangInATest {
        @Test
        void hangs() {
            Spin.forever();
        }
    }

    @EnabledIfSystemProperty(named = ENABLED_PROPERTY, matches = "true")
    static final class HangInADynamicTest {
        @TestFactory
        Stream<DynamicTest> hangs() {
            return Stream.of(DynamicTest.dynamicTest("spins", Spin::forever));
        }
    }

    @EnabledIfSystemProperty(named = ENABLED_PROPERTY, matches = "true")
    static final class HangInBeforeAll {
        @BeforeAll
        static void hangs() {
            Spin.forever();
        }

        @Test
        void neverReached() {
        }
    }

    @EnabledIfSystemProperty(named = ENABLED_PROPERTY, matches = "true")
    static final class HangInAfterAll {
        @AfterAll
        static void hangs() {
            Spin.forever();
        }

        @Test
        void passes() {
        }
    }

    @EnabledIfSystemProperty(named = ENABLED_PROPERTY, matches = "true")
    static final class HangInATemplateInvocation {
        @ParameterizedTest
        @ValueSource(ints = {1, 2})
        void hangs(int invocation) {
            Spin.forever();
        }
    }

    @EnabledIfSystemProperty(named = ENABLED_PROPERTY, matches = "true")
    static final class HangInAStaticInitializer {
        static {
            Spin.foreverIfAsked();
        }

        @Test
        void neverReached() {
        }
    }

    /** Longer in all than the limit it runs under, every part of it far shorter. */
    @EnabledIfSystemProperty(named = ENABLED_PROPERTY, matches = "true")
    static final class LongAndWellBehaved {
        private static final int PART_MILLIS = 400;

        @BeforeAll
        static void settles() throws InterruptedException {
            Thread.sleep(PART_MILLIS);
        }

        @Test
        void first() throws InterruptedException {
            Thread.sleep(PART_MILLIS);
        }

        @Test
        void second() throws InterruptedException {
            Thread.sleep(PART_MILLIS);
        }

        @Test
        void third() throws InterruptedException {
            Thread.sleep(PART_MILLIS);
        }

        @Test
        void fourth() throws InterruptedException {
            Thread.sleep(PART_MILLIS);
        }

        @Test
        void fifth() throws InterruptedException {
            Thread.sleep(PART_MILLIS);
        }

        @TestFactory
        Stream<DynamicTest> many() {
            return IntStream.range(0, 5).mapToObj(index -> DynamicTest.dynamicTest("part " + index,
                    () -> Thread.sleep(PART_MILLIS)));
        }

        @ParameterizedTest
        @ValueSource(ints = {1, 2, 3, 4})
        void each(int invocation) throws InterruptedException {
            Thread.sleep(PART_MILLIS);
        }
    }
}
