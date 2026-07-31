package souther.bench;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.function.Consumer;

/**
 * A repeated measurement, reported as an order statistic rather than a mean.
 *
 * <p>A compile allocates enough to be interrupted by a collection, so the distribution has a tail
 * and a mean sits inside it. The median says what a run usually costs, the minimum says what it
 * costs when nothing interferes, and the difference between them is how much of the number is the
 * machine rather than the compiler.
 */
public record Timing(List<Long> micros) {

    /** Runs {@code work} to warm the JIT, then times it, discarding the warm-up. */
    public static Timing of(int warmup, int measured, Runnable work) {
        for (int i = 0; i < warmup; i++) {
            work.run();
        }
        List<Long> micros = new ArrayList<>();
        for (int i = 0; i < measured; i++) {
            long start = System.nanoTime();
            work.run();
            micros.add((System.nanoTime() - start) / 1000);
        }
        return new Timing(micros);
    }

    /**
     * The same, where each run needs setting up first and the set-up must not be timed — an edit is
     * measured this way, because the store it is applied to has to be brought back to the state the
     * edit starts from.
     */
    public static Timing ofPrepared(int warmup, int measured, Consumer<Integer> work) {
        List<Long> micros = new ArrayList<>();
        for (int i = 0; i < warmup + measured; i++) {
            long start = System.nanoTime();
            work.accept(i);
            long spent = (System.nanoTime() - start) / 1000;
            if (i >= warmup) {
                micros.add(spent);
            }
        }
        return new Timing(micros);
    }

    public double medianMillis() {
        return at(0.5);
    }

    public double minMillis() {
        return at(0.0);
    }

    public double p90Millis() {
        return at(0.9);
    }

    private double at(double quantile) {
        List<Long> sorted = new ArrayList<>(micros);
        Collections.sort(sorted);
        int index = Math.min(sorted.size() - 1, (int) (sorted.size() * quantile));
        return sorted.get(index) / 1000.0;
    }
}
