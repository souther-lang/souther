package souther.test;

import static org.junit.platform.engine.discovery.DiscoverySelectors.selectClass;
import static org.junit.platform.launcher.core.LauncherDiscoveryRequestBuilder.request;

import org.junit.platform.engine.FilterResult;
import org.junit.platform.engine.discovery.ClassNameFilter;
import org.junit.platform.launcher.core.LauncherDiscoveryRequestBuilder;
import org.junit.platform.launcher.core.LauncherFactory;
import org.junit.platform.launcher.listeners.SummaryGeneratingListener;
import org.junit.platform.launcher.listeners.TestExecutionSummary;

/**
 * The JVM {@code TheWatchdogStopsWhatDoesNotComeBackTest} starts: it runs one fixture through the
 * launcher as surefire does, with the listeners the launcher finds itself. It exits 0 when the
 * fixture ran and passed; a fixture the watchdog stops never gets that far.
 */
public final class WatchdogChild {

    /** Asks for discovery that does not return, in place of a fixture that does not. */
    static final String HANGING_DISCOVERY = "discovery";

    private WatchdogChild() {
    }

    /** The first argument names the fixture class; the second, if present, is the mode. */
    public static void main(String[] args) {
        LauncherDiscoveryRequestBuilder builder = request().selectors(selectClass(args[0]));
        if (args.length > 1 && args[1].equals(HANGING_DISCOVERY)) {
            builder = builder.filters(new HangingFilter());
        }
        SummaryGeneratingListener summary = new SummaryGeneratingListener();
        LauncherFactory.create().execute(builder.build(), summary);
        TestExecutionSummary result = summary.getSummary();
        boolean passed = result.getTestsSucceededCount() > 0 && result.getTestsFailedCount() == 0
                && result.getContainersFailedCount() == 0;
        System.out.println("ran " + result.getTestsSucceededCount() + " tests");
        System.exit(passed ? 0 : 1);
    }

    /** A filter the engine asks while discovering, which never answers. */
    private static final class HangingFilter implements ClassNameFilter {
        @Override
        public FilterResult apply(String className) {
            WatchdogFixtures.Spin.forever();
            return FilterResult.included("never reached");
        }
    }
}
