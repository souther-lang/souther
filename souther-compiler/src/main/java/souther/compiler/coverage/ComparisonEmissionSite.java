package souther.compiler.coverage;

/**
 * Where a run through one comparison is recorded, which is a number the instrumentation hands out.
 *
 * <p>An address and not an identity. What a probed class calls is {@code Probe.compared} with an
 * {@code int}, and what comes back from a recording is that {@code int} — so this is the vocabulary
 * a run is written and read in, and it reaches no further. Which comparison a reading is talking
 * about is {@link ComparisonOccurrence}, and the two are held apart because they are answered by
 * different things: the plan hands out an address for the comparisons it instruments, and the
 * catalog names every comparison the bodies hold whether anything instruments it or not.
 *
 * <p>Kept as one value rather than as the {@code int} it wraps, so that an address cannot be handed
 * where an identity is wanted. Under one type the two were the same number, and a reading that
 * asked which comparison it was looking at got an answer that was true only while every comparison
 * the catalog held was one the emitter had numbered.
 *
 * @param value the number the emitter writes into the call and a recording reads back
 */
public record ComparisonEmissionSite(int value) {

    public ComparisonEmissionSite {
        if (value < 0) {
            throw new IllegalArgumentException(
                    "a place a run is recorded at is a place the emitter numbered: " + value);
        }
    }

    @Override
    public String toString() {
        return "site@" + value;
    }
}
