package souther.test;

import java.util.Optional;
import org.junit.platform.launcher.LauncherDiscoveryListener;
import org.junit.platform.launcher.LauncherDiscoveryRequest;

/**
 * Puts the launcher's discovery of tests under {@link TestWatchdog}. No test is executing while
 * the engines look for them, so the execution events the watchdog reads say nothing about it;
 * discovery is announced by its own listener, and this watches from its start to its end.
 *
 * <p>Registered through {@code META-INF/services}, like the watchdog.
 */
public final class TestDiscoveryWatchdog implements LauncherDiscoveryListener {

    @Override
    public void launcherDiscoveryStarted(LauncherDiscoveryRequest request) {
        TestWatchdog.running().started(idOf(request), Optional.empty(), "discovery of tests");
    }

    @Override
    public void launcherDiscoveryFinished(LauncherDiscoveryRequest request) {
        TestWatchdog.running().finished(idOf(request));
    }

    private static String idOf(LauncherDiscoveryRequest request) {
        return "discovery@" + System.identityHashCode(request);
    }
}
