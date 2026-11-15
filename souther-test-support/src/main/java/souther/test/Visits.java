package souther.test;

import jdk.jfr.FlightRecorder;
import jdk.jfr.Recording;
import jdk.jfr.consumer.RecordedEvent;
import jdk.jfr.consumer.RecordedMethod;
import jdk.jfr.consumer.RecordingFile;
import org.junit.jupiter.api.Assumptions;

import java.io.IOException;
import java.io.UncheckedIOException;
import java.nio.file.Files;
import java.nio.file.Path;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.function.Supplier;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * How many times work went into the methods of some classes, for a test that holds a walk over
 * values to visiting each part once.
 *
 * <p>A walk over a graph of values that reaches a part by every way to it visits the shared parts
 * once per way. What a walk allocates does not tell that: a reader that only descends allocates
 * nothing. Every descent into a value goes through a method of its class, an accessor or a method of
 * the value, so the entries into those methods are what the walk visited, and they are the same on
 * every run whatever else the machine is doing. The data is the test's own and needs no counting
 * wrapper, which the values that hold their parts in fields cannot have.
 *
 * <p>A walk that reaches the values only through their private fields enters no method of them and
 * is not seen; a reader that does so inside the counted classes is seen through its own entries.
 * Counts are of one-time work as well as repeated work, so a test asks for growth between sizes,
 * with a floor under which a count says nothing, and not for a count of its own.
 *
 * <p>The entries are counted by the JVM's method timing, which is asked for the classes of the
 * values and the classes nested in them. The timing is the JVM's and has no thread in it, so a
 * count is of every thread: a worker another test left running the counted classes, or one this
 * test started, adds its entries to the count of whatever is being counted while it runs. A test
 * that counts leaves no worker running the counted classes (one already running when the counter
 * is opened fails its calibration, one that starts later is not seen), and one that fails on a count being
 * too high asks {@link #duringLeast} so that a stray thread in one counting cannot fail it. A count
 * of nothing is a state a test of a cost has to tell
 * from a counter that is not counting, so the counter is asked to count a visit of known number when
 * it is opened and refuses to be used if it did not.
 */
public final class Visits implements AutoCloseable {

    /** What the counter is calibrated on. */
    private record Calibration(int part) {}

    private static final int CALIBRATION_VISITS = 7;

    /** A reading takes the whole recording, so a recording that has been read this often is
     *  replaced by a new one and the readings do not grow with how many were taken. */
    private static final int READINGS_PER_RECORDING = 40;

    private final String filter;

    private Recording recording;

    private int readings;

    private long counted;

    private Visits(String filter) {
        this.filter = filter;
    }

    /** What was worked out, and how many times it went into the classes while it was. */
    public record Counted<T>(T value, long visits) {}

    /**
     * A counter of the entries into the classes of {@code types}, and those nested in them and
     * sharing a nest with them.
     */
    public static Visits into(Collection<Class<?>> types) {
        Assumptions.assumeTrue(FlightRecorder.isAvailable(), "this JVM has no flight recorder");
        Set<String> names = new LinkedHashSet<>();
        names.add(Calibration.class.getName());
        for (Class<?> type : types) {
            addNest(type.getNestHost(), names);
        }
        Visits visits = new Visits(String.join(";", names));
        try {
            visits.record();
            visits.calibrate();
            return visits;
        } catch (RuntimeException | Error failed) {
            visits.close();
            throw failed;
        }
    }

    private void record() {
        if (recording != null) {
            recording.close();
        }
        recording = new Recording();
        recording.enable("jdk.MethodTiming").with("filter", filter).with("period", "endChunk");
        recording.start();
        readings = 0;
        counted = entriesSoFar();
    }

    private static void addNest(Class<?> owner, Set<String> into) {
        into.add(owner.getName());
        for (Class<?> nested : owner.getDeclaredClasses()) {
            addNest(nested, into);
        }
    }

    private void calibrate() {
        Calibration known = new Calibration(1);
        counted = entriesSoFar();
        Counted<Integer> seen = count(() -> {
            int sum = 0;
            for (int at = 0; at < CALIBRATION_VISITS; at++) {
                sum += known.part();
            }
            return sum;
        });
        assertEquals(CALIBRATION_VISITS, seen.visits(), "the counter reported " + seen.visits()
                + " entries for " + CALIBRATION_VISITS + " visits of a value, so it is not counting"
                + " (or another thread is running the classes it counts)");
    }

    /** What {@code work} came to, and how many times it went into the classes while it did. */
    public <T> Counted<T> count(Supplier<T> work) {
        long before = counted;
        T value = work.get();
        long now = entriesSoFar();
        readings++;
        if (readings >= READINGS_PER_RECORDING) {
            record();
        } else {
            counted = now;
        }
        return new Counted<>(value, now - before);
    }

    /** How many times {@code work} went into the classes. */
    public long during(Runnable work) {
        return count(() -> {
            work.run();
            return Boolean.TRUE;
        }).visits();
    }

    /**
     * The smaller of two countings of {@code work}, which is done twice.
     *
     * <p>For a count a test fails on when it is high. What another thread adds to one counting is
     * not there in the other unless that thread is running through both, so a count that is over
     * only because of a stray thread is not over here. Work that keeps something of what it did
     * counts less the second time, which can only lower the answer.
     */
    public long duringLeast(Runnable work) {
        return Math.min(during(work), during(work));
    }

    private long entriesSoFar() {
        try (Recording snapshot = FlightRecorder.getFlightRecorder().takeSnapshot()) {
            Path dump = Files.createTempFile("visits", ".jfr");
            try {
                snapshot.dump(dump);
                Map<String, Long> byMethod = new HashMap<>();
                for (RecordedEvent event : RecordingFile.readAllEvents(dump)) {
                    if (event.getEventType().getName().equals("jdk.MethodTiming")) {
                        RecordedMethod method = event.getValue("method");
                        byMethod.merge(method.getType().getName() + "." + method.getName()
                                + method.getDescriptor(), event.getLong("invocations"), Math::max);
                    }
                }
                return byMethod.values().stream().mapToLong(Long::longValue).sum();
            } finally {
                Files.deleteIfExists(dump);
            }
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
    }

    @Override
    public void close() {
        if (recording != null) {
            recording.close();
        }
    }
}
