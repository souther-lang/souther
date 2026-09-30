package souther.compiler.regex;

import java.util.List;
import souther.runtime.StringPattern;

/**
 * The machine a class runs for a pattern, as the image a class holds, or why there is none.
 *
 * <p>The one place a pattern becomes what a run executes. Every backend consumer — a
 * {@code String.matches} call, a decoder's format constraint — asks here, so which machine a class
 * runs and how it is written are decided once.
 *
 * <p>The deterministic machine where making it stays within {@link PatternPlan.Budget#OF_A_DETERMINISTIC_RUN}
 * and its image within {@link #MOST_CHARACTERS}; otherwise the machine the pattern's shape builds,
 * steps for nothing and all. Both accept the same strings, so which one a class holds decides how
 * fast a run is and nothing about its answer. Only the shape's machine can refuse a pattern: past
 * {@link PatternPlan.Budget#OF_A_RUN}, or past the characters a class is given for one image, there
 * is no machine this backend writes.
 */
public sealed interface PatternImage {

    /**
     * The most characters one pattern's image may take.
     *
     * <p>What a class is given for it, and not a limit of the class file's: the image is cut into
     * strings each a class holds ({@link StringPattern#CHUNK}), and this keeps the number of those
     * small beside the constants the rest of the class refers to.
     */
    int MOST_CHARACTERS = 1 << 20;

    /** The image, as the strings the class holds it in. */
    record Written(List<String> strings) implements PatternImage {

        public Written {
            strings = List.copyOf(strings);
        }
    }

    /** The machine the shape builds has more states than {@code most}. */
    record MoreStates(int most) implements PatternImage {}

    /** The machine the shape builds is written in more characters than {@code most}. */
    record MoreCharacters(int most) implements PatternImage {}

    /** What a class runs for {@code meaning}. */
    static PatternImage of(PatternMeaning meaning) {
        Automaton shaped = Automaton.of(meaning, PatternPlan.Budget.OF_A_RUN.meter());
        if (shaped == null) {
            return new MoreStates(PatternPlan.Budget.OF_A_RUN.mostStates());
        }
        Automaton one = shaped.canonical(PatternPlan.Budget.OF_A_DETERMINISTIC_RUN.meter());
        if (one != null) {
            List<String> image = written(one, true);
            if (fits(image)) {
                return new Written(image);
            }
        }
        List<String> image = written(shaped, false);
        return fits(image) ? new Written(image) : new MoreCharacters(MOST_CHARACTERS);
    }

    /**
     * The deterministic machine's image, or null where making it is past {@code meter}.
     *
     * <p>For a check holding the two images against each other. {@link #of} picks by size, so a
     * small pattern only ever reaches the deterministic one there, and the other would go unasked.
     */
    static List<String> deterministic(PatternMeaning meaning, Meter meter) {
        Automaton shaped = Automaton.of(meaning, meter);
        Automaton one = shaped == null ? null : shaped.canonical(meter);
        return one == null ? null : written(one, true);
    }

    /** The shape's machine's image, or null where it is past {@code meter}. See
     *  {@link #deterministic}. */
    static List<String> shaped(PatternMeaning meaning, Meter meter) {
        Automaton shaped = Automaton.of(meaning, meter);
        return shaped == null ? null : written(shaped, false);
    }

    private static boolean fits(List<String> image) {
        long characters = 0;
        for (String each : image) {
            characters += each.length();
        }
        return characters <= MOST_CHARACTERS;
    }

    private static List<String> written(Automaton machine, boolean deterministic) {
        StringPattern.Writer out = new StringPattern.Writer(deterministic);
        for (int state = 0; state < machine.size(); state++) {
            out.state(machine.stopsAt(state));
        }
        for (int state = 0; state < machine.size(); state++) {
            for (Automaton.Step each : machine.stepsFrom(state)) {
                List<CodePoints.Range> ranges = each.over().ranges();
                int[] pairs = new int[ranges.size() * 2];
                for (int at = 0; at < ranges.size(); at++) {
                    pairs[at * 2] = ranges.get(at).from();
                    pairs[at * 2 + 1] = ranges.get(at).to();
                }
                out.step(state, out.set(pairs), each.to());
            }
            for (int to : machine.freeFrom(state)) {
                out.free(state, to);
            }
        }
        return out.image();
    }
}
