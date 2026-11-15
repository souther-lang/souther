package souther.test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertTrue;

import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import org.junit.jupiter.api.BeforeAll;
import org.junit.jupiter.api.Test;
import org.junit.jupiter.params.ParameterizedTest;
import org.junit.jupiter.params.provider.ValueSource;

/**
 * The watchdog as a build meets it: a JVM that runs a launcher over a test that does not come
 * back, with the listeners the launcher finds itself, ends with the watchdog's status and says
 * where it was stuck. One JVM for each place JUnit runs code, run side by side; a long class whose
 * every part is short runs in one more and must pass under the same limit.
 *
 * <p>The parent only waits for the children. It reads no clock: a child that is not stopped leaves
 * this test running, which the watchdog of the JVM this runs in then ends.
 */
class TheWatchdogStopsWhatDoesNotComeBackTest {

    private static final int HALTED = 70;
    /** Past what the long class takes in any one part by far, and under what it takes in all. */
    private static final String LIMIT_SECONDS = "5";
    private static final String FIXTURES = "souther.test.WatchdogFixtures$";

    /** How a child JVM ended and what it said. */
    private record Outcome(int exitStatus, String stderr) {
    }

    private static final Map<String, Outcome> OUTCOMES = new LinkedHashMap<>();

    @BeforeAll
    static void runEveryShapeSideBySide() throws IOException, InterruptedException {
        List<String> names = List.of("HangInATest", "HangInADynamicTest", "HangInBeforeAll",
                "HangInAfterAll", "HangInATemplateInvocation", "HangInAStaticInitializer",
                "LongAndWellBehaved");
        Map<String, Process> started = new LinkedHashMap<>();
        Map<String, Path> stderrs = new LinkedHashMap<>();
        for (String name : names) {
            start(name, List.of(), started, stderrs);
        }
        start("HangInATest", List.of(WatchdogChild.HANGING_DISCOVERY), started, stderrs,
                "HangingDiscovery");
        for (Map.Entry<String, Process> child : started.entrySet()) {
            int exitStatus = child.getValue().waitFor();
            Path stderr = stderrs.get(child.getKey());
            OUTCOMES.put(child.getKey(), new Outcome(exitStatus, Files.readString(stderr)));
            Files.delete(stderr);
        }
    }

    private static void start(String fixture, List<String> mode, Map<String, Process> started,
            Map<String, Path> stderrs) throws IOException {
        start(fixture, mode, started, stderrs, fixture);
    }

    private static void start(String fixture, List<String> mode, Map<String, Process> started,
            Map<String, Path> stderrs, String key) throws IOException {
        List<String> command = new ArrayList<>(List.of(
                Path.of(System.getProperty("java.home"), "bin", "java").toString(),
                "-D" + TestWatchdog.LIMIT_PROPERTY + "=" + LIMIT_SECONDS,
                "-D" + WatchdogFixtures.ENABLED_PROPERTY + "=true",
                "-cp", System.getProperty("java.class.path"),
                WatchdogChild.class.getName(), FIXTURES + fixture));
        command.addAll(mode);
        Path stderr = Files.createTempFile("watchdog-child", ".err");
        started.put(key, new ProcessBuilder(command)
                .redirectError(stderr.toFile())
                .redirectOutput(ProcessBuilder.Redirect.DISCARD)
                .start());
        stderrs.put(key, stderr);
    }

    @ParameterizedTest
    @ValueSource(strings = {"HangInATest", "HangInADynamicTest", "HangInBeforeAll",
            "HangInAfterAll", "HangInATemplateInvocation", "HangInAStaticInitializer"})
    void aHangInEachPlaceJUnitRunsCodeIsStoppedAndNamed(String fixture) {
        Outcome outcome = OUTCOMES.get(fixture);
        assertEquals(HALTED, outcome.exitStatus(), outcome.stderr());
        assertTrue(outcome.stderr().contains(FIXTURES + fixture), outcome.stderr());
        assertTrue(outcome.stderr().contains("Spin.forever"), outcome.stderr());
    }

    @Test
    void aHangInDiscoveryIsStoppedAndNamed() {
        Outcome outcome = OUTCOMES.get("HangingDiscovery");
        assertEquals(HALTED, outcome.exitStatus(), outcome.stderr());
        assertTrue(outcome.stderr().contains("discovery of tests"), outcome.stderr());
        assertTrue(outcome.stderr().contains("HangingFilter"), outcome.stderr());
    }

    @Test
    void aClassLongerInAllThanTheLimitButShortInEveryPartIsNotStopped() {
        Outcome outcome = OUTCOMES.get("LongAndWellBehaved");
        assertEquals(0, outcome.exitStatus(), outcome.stderr());
        assertFalse(outcome.stderr().contains("TestWatchdog"), outcome.stderr());
    }

    @Test
    void thisForksLauncherRegisteredTheWatchdogAndIsWatchingThisTest() {
        assertTrue(TestWatchdog.runningNow().stream()
                        .anyMatch(name -> name.contains(TheWatchdogStopsWhatDoesNotComeBackTest.class.getName())),
                TestWatchdog.runningNow().toString());
    }
}
