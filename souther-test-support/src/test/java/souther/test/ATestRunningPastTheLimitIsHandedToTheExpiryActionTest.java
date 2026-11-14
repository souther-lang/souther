package souther.test;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.atomic.AtomicLong;
import org.junit.jupiter.api.Test;

/** Which running tests are past the limit, read off a clock the test moves itself. */
class ATestRunningPastTheLimitIsHandedToTheExpiryActionTest {

    private final AtomicLong clock = new AtomicLong();
    private final List<TestWatchdog.Expired> expired = new ArrayList<>();
    private final TestWatchdog.Running running = new TestWatchdog.Running(
            clock::get, Duration.ofSeconds(10), expired::add);

    @Test
    void onlyATestPastTheLimitIsHandedOnAndWithHowLongItRan() {
        running.began("slow", "slow of A");
        clock.set(Duration.ofSeconds(6).toNanos());
        running.began("fast", "fast of A");
        clock.set(Duration.ofSeconds(11).toNanos());
        running.look();
        assertEquals(List.of(new TestWatchdog.Expired("slow of A", Duration.ofSeconds(11))), expired);
    }

    @Test
    void aTestAtTheLimitExactlyIsNotPastIt() {
        running.began("edge", "edge of A");
        clock.set(Duration.ofSeconds(10).toNanos());
        running.look();
        assertEquals(List.of(), expired);
    }

    @Test
    void aTestThatEndedIsNotLookedAtAgain() {
        running.began("done", "done of A");
        running.ended("done");
        clock.set(Duration.ofHours(1).toNanos());
        running.look();
        assertEquals(List.of(), expired);
    }
}
