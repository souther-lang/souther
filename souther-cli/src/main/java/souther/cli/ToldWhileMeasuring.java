package souther.cli;

import souther.compiler.diag.Messages;
import souther.compiler.query.Compilation;
import souther.compiler.query.WhatIsBeingMeasured;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Optional;
import java.util.concurrent.Executors;
import java.util.concurrent.ScheduledExecutorService;
import java.util.concurrent.ScheduledFuture;
import java.util.concurrent.TimeUnit;

/**
 * What a run that measures says on the error stream while its author waits: what it measures,
 * once the wait is long enough to be one, and which behavior it is on at each minute after.
 *
 * <p>A run that ends sooner says nothing here, so a short run writes what it wrote before. The
 * measurement is not held to any length: what is said is where the time is going, which is what
 * tells an author which behavior to look at.
 */
final class ToldWhileMeasuring implements AutoCloseable {

    /** How long a run measures before it says what it measures. */
    static final long SAYS_WHAT_IT_MEASURES_AFTER_SECONDS = 5;
    /** How often after that it says which behavior it is on. */
    static final long SAYS_WHERE_IT_IS_EVERY_SECONDS = 60;

    private final PrintStream err;
    private final Locale locale;
    private final WhatIsBeingMeasured where = new WhatIsBeingMeasured();
    private final ScheduledExecutorService clock = Executors.newSingleThreadScheduledExecutor(
            work -> {
                Thread thread = new Thread(work, "souther-told-while-measuring");
                thread.setDaemon(true);
                return thread;
            });
    /** The telling that is due each second, once the measurement has begun. */
    private ScheduledFuture<?> telling;
    private Map<String, List<String>> measured = Map.of();
    private boolean saidWhat;
    private long timesSaidWhere;

    ToldWhileMeasuring(PrintStream err, Locale locale) {
        this.err = err;
        this.locale = locale;
    }

    /** The measurement of {@code compilation} begins: it is listened to from here, and the time
     *  it takes is counted from here. */
    void begin(Compilation compilation) {
        listenTo(compilation);
        long began = System.nanoTime();
        telling = clock.scheduleAtFixedRate(
                () -> after(TimeUnit.NANOSECONDS.toSeconds(System.nanoTime() - began)),
                1, 1, TimeUnit.SECONDS);
    }

    /** As {@link #begin}, with nothing counting the time: whoever calls says how long it has
     *  been ({@link #after}). */
    synchronized void listenTo(Compilation compilation) {
        measured = WhatIsBeingMeasured.toBeMeasuredIn(compilation);
        compilation.tell(where);
    }

    /** Says what is due {@code seconds} into the measurement and has not been said. */
    synchronized void after(long seconds) {
        if (!saidWhat && seconds >= SAYS_WHAT_IT_MEASURES_AFTER_SECONDS) {
            saidWhat = true;
            err.println(Messages.get("cli.examples.measuring", locale, whatIsMeasured()));
        }
        long due = seconds / SAYS_WHERE_IT_IS_EVERY_SECONDS;
        if (due > timesSaidWhere) {
            timesSaidWhere = due;
            long minutes = TimeUnit.SECONDS.toMinutes(seconds);
            err.println(whereItIs(minutes, where.now()));
        }
    }

    private String whereItIs(long minutes, Optional<WhatIsBeingMeasured.Work> now) {
        if (now.isEmpty()) {
            return Messages.get("cli.examples.measuring.still", locale, minutes);
        }
        WhatIsBeingMeasured.Work work = now.get();
        return work.reading().equals(work.asked())
                ? Messages.get("cli.examples.measuring.now", locale, minutes, named(work.asked()))
                : Messages.get("cli.examples.measuring.reading", locale, minutes,
                        named(work.asked()), named(work.reading()));
    }

    private String whatIsMeasured() {
        List<String> each = new ArrayList<>();
        measured.forEach((module, behaviors) -> each.add(behaviors.size() == 1
                ? "`" + module + "." + behaviors.get(0) + "`"
                : Messages.get("cli.examples.measuring.module", locale, module,
                        behaviors.size())));
        return String.join(", ", each);
    }

    private static String named(WhatIsBeingMeasured.Subject subject) {
        return "`" + subject.module() + subject.behavior().map(name -> "." + name).orElse("")
                + "`";
    }

    @Override
    public void close() {
        if (telling != null) {
            telling.cancel(false);
        }
        clock.shutdownNow();
    }
}
