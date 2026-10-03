package souther.compiler.check;

import java.util.Map;
import java.util.concurrent.ConcurrentHashMap;
import java.util.concurrent.atomic.AtomicLong;

/**
 * Where {@link SettledWork#done} counts what it works out, by the kind of work.
 *
 * <p>Its own class because an interface has no private state, and a count anybody could reset is
 * not one a test can hold a reader to.
 */
final class SettledWorkDone {

    private static final Map<Class<?>, AtomicLong> DONE = new ConcurrentHashMap<>();

    static void count(Class<?> kind) {
        DONE.computeIfAbsent(kind, _ -> new AtomicLong()).incrementAndGet();
    }

    static long of(Class<?> kind) {
        AtomicLong done = DONE.get(kind);
        return done == null ? 0 : done.get();
    }

    private SettledWorkDone() {}
}
