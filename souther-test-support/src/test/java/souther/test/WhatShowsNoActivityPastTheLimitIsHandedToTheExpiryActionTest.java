package souther.test;

import static org.junit.jupiter.api.Assertions.assertEquals;

import java.time.Duration;
import java.util.ArrayList;
import java.util.List;
import java.util.Optional;
import java.util.concurrent.atomic.AtomicLong;
import org.junit.jupiter.api.Test;

/** What is past the limit, read off a clock the test moves itself. */
class WhatShowsNoActivityPastTheLimitIsHandedToTheExpiryActionTest {

    private static final Optional<String> NONE = Optional.empty();

    private final AtomicLong clock = new AtomicLong();
    private final List<List<TestWatchdog.Expired>> expired = new ArrayList<>();
    private final TestWatchdog.Running running = new TestWatchdog.Running(
            clock::get, Duration.ofSeconds(10), expired::add);

    private void advanceTo(long seconds) {
        clock.set(Duration.ofSeconds(seconds).toNanos());
    }

    @Test
    void onlyATestPastTheLimitIsHandedOnAndWithHowLongItIdled() {
        running.started("slow", NONE, "slow");
        advanceTo(6);
        running.started("fast", NONE, "fast");
        advanceTo(11);
        running.look();
        assertEquals(List.of(List.of(new TestWatchdog.Expired("slow", Duration.ofSeconds(11)))),
                expired);
    }

    @Test
    void aTestAtTheLimitExactlyIsNotPastIt() {
        running.started("edge", NONE, "edge");
        advanceTo(10);
        running.look();
        assertEquals(List.of(), expired);
    }

    @Test
    void aTestThatFinishedIsNotLookedAtAgain() {
        running.started("done", NONE, "done");
        running.finished("done");
        advanceTo(3600);
        running.look();
        assertEquals(List.of(), expired);
    }

    @Test
    void aContainerWhoseChildrenKeepComingAndGoingIsNotStuck() {
        running.started("class", NONE, "class");
        for (int second = 1; second <= 40; second += 4) {
            advanceTo(second);
            running.started("test" + second, Optional.of("class"), "test");
            advanceTo(second + 2);
            running.finished("test" + second);
            running.look();
        }
        assertEquals(List.of(), expired);
    }

    @Test
    void aContainerWithNoChildStartingOrFinishingIsStuckAndNamedAfterWhatIsBeneathIt() {
        running.started("engine", NONE, "engine");
        running.started("class", Optional.of("engine"), "class");
        advanceTo(5);
        running.started("factory", Optional.of("class"), "factory");
        running.started("dynamic", Optional.of("factory"), "dynamic");
        advanceTo(16);
        running.look();
        assertEquals(List.of(List.of(
                new TestWatchdog.Expired("dynamic", Duration.ofSeconds(11)),
                new TestWatchdog.Expired("factory", Duration.ofSeconds(11)),
                new TestWatchdog.Expired("class", Duration.ofSeconds(11)),
                new TestWatchdog.Expired("engine", Duration.ofSeconds(11)))), expired);
    }

    @Test
    void aClassHangingBeforeItsFirstTestIsStuckFromItsOwnStart() {
        running.started("engine", NONE, "engine");
        running.started("class", Optional.of("engine"), "class");
        advanceTo(11);
        running.look();
        assertEquals(List.of(
                new TestWatchdog.Expired("class", Duration.ofSeconds(11)),
                new TestWatchdog.Expired("engine", Duration.ofSeconds(11))), expired.get(0));
    }

    @Test
    void theLastChildFinishingMakesTheClassActiveAndSoItsAfterAllIsAgedFromThere() {
        running.started("class", NONE, "class");
        running.started("test", Optional.of("class"), "test");
        advanceTo(9);
        running.finished("test");
        advanceTo(15);
        running.look();
        assertEquals(List.of(), expired);
        advanceTo(20);
        running.look();
        assertEquals(List.of(List.of(new TestWatchdog.Expired("class", Duration.ofSeconds(11)))),
                expired);
    }

    @Test
    void aSkippedChildIsActivityOfTheContainerAboveIt() {
        running.started("class", NONE, "class");
        advanceTo(9);
        running.activityBeneath(Optional.of("class"));
        advanceTo(15);
        running.look();
        assertEquals(List.of(), expired);
    }

    @Test
    void whatIsWatchedIsNamed() {
        running.started("a", NONE, "name of a");
        running.started("b", Optional.of("a"), "name of b");
        assertEquals(List.of("name of a", "name of b"),
                running.names().stream().sorted().toList());
    }
}
