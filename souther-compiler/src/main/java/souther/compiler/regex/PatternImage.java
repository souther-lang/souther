package souther.compiler.regex;

import java.util.IdentityHashMap;
import java.util.List;
import java.util.Map;
import souther.runtime.StringPattern;

/**
 * The machine a class runs for a pattern, as the image a class holds, or why there is none.
 *
 * <p>The one place a pattern becomes what a run executes. Every backend consumer — a
 * {@code String.matches} call, a decoder's format constraint — asks here, so which machine a class
 * runs and how it is written are decided once.
 *
 * <p>The deterministic machine where making it stays within
 * {@link PatternPlan.Budget#OF_A_DETERMINISTIC_RUN} — its states and the work of making them — and
 * its image within {@link #MOST_CHARACTERS}; otherwise the machine the pattern's shape builds,
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
     *
     * <p>Above what the largest machine {@link PatternPlan.Budget#OF_A_RUN} lets the shape build
     * takes where its steps are over sets a pattern writes once — a repetition written out, which is
     * what makes a shape large. So what this refuses is a pattern whose sets are themselves large,
     * and never one the state limit already let through for its size alone.
     */
    int MOST_CHARACTERS = 1 << 23;

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
        // Trying costs what the meter counts — the rows, as wide as the symbols the shape tells
        // apart and as deep as the subsets they are worked out from — and stops where that runs
        // out, so a shape nothing deterministic is worth making is given up on early.
        Automaton one = shaped.canonical(PatternPlan.Budget.OF_A_DETERMINISTIC_RUN.meter());
        List<String> image = one == null ? null : written(one, true);
        if (image == null) {
            image = written(shaped, false);
        }
        return image == null ? new MoreCharacters(MOST_CHARACTERS) : new Written(image);
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

    /**
     * {@code machine}'s image, or null where it would take more than {@link #MOST_CHARACTERS}.
     *
     * <p>Stopped where the writer says it is past its limit, which is before the next state is
     * written: what is refused here is never written out first. A label is handed to the writer once
     * however many steps share it.
     */
    private static List<String> written(Automaton machine, boolean deterministic) {
        StringPattern.Writer out = new StringPattern.Writer(deterministic, MOST_CHARACTERS);
        for (int state = 0; state < machine.size() && out.holds(); state++) {
            out.state(machine.stopsAt(state));
        }
        Map<CodePoints, Integer> sets = new IdentityHashMap<>();
        for (int state = 0; state < machine.size() && out.holds(); state++) {
            for (Automaton.Step each : machine.stepsFrom(state)) {
                Integer set = sets.get(each.over());
                if (set == null) {
                    set = out.set(pairs(each.over()));
                    sets.put(each.over(), set);
                }
                out.step(state, set, each.to());
            }
            for (int to : machine.freeFrom(state)) {
                out.free(state, to);
            }
        }
        return out.holds() ? out.image() : null;
    }

    private static int[] pairs(CodePoints over) {
        List<CodePoints.Range> ranges = over.ranges();
        int[] out = new int[ranges.size() * 2];
        for (int at = 0; at < ranges.size(); at++) {
            out[at * 2] = ranges.get(at).from();
            out[at * 2 + 1] = ranges.get(at).to();
        }
        return out;
    }
}
