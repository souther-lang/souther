package souther.compiler.regex;

import java.util.Map;
import java.util.Optional;
import java.util.concurrent.ConcurrentHashMap;
import net.unit8.notation199x.pattern.Automaton;
import net.unit8.notation199x.pattern.Meter;
import net.unit8.notation199x.pattern.PatternMeaning;

/**
 * Whether a string is one a pattern means, answered by walking the machine the meaning builds.
 *
 * <p>Not a {@link Language}. A language is an answer about the strings a position admits, made
 * canonical so that two of them compare, and what it costs is what its position was allowed. This
 * answers one question of one string — what the compiler folds {@code String.matches} over a written
 * subject to — so it builds the machine the meaning is and walks it, and nothing is made canonical
 * that nobody compares.
 */
public final class Recognizer {

    /**
     * What each pattern means, as the machine a walk goes over. A declaration's pattern is asked
     * about once per construction from it and once per reading of a branch, and building the
     * machine is the only expensive thing here. Keyed by the meaning, so two spellings of one
     * pattern are one machine.
     */
    private static final Map<Object, Optional<Recognizer>> BUILT = new ConcurrentHashMap<>();

    private final Automaton machine;

    private Recognizer(Automaton machine) {
        this.machine = machine;
    }

    /**
     * Whether {@code value} is one of the strings {@code meaning} denotes, or empty where the
     * machine for it is more than a fold may build, or walking {@code value} over it more than a
     * fold may look at.
     */
    public static Optional<Boolean> recognizes(PatternMeaning meaning, String value) {
        return recognizes(meaning, meaning, value);
    }

    /**
     * The same, with the machine kept under {@code key} where hashing {@code meaning} for every
     * string asked is a cost the asker can avoid: a meaning is a tree of records, hashed and
     * compared in full, and a key that spells it once is hashed in a string's cached hash.
     * Two keys that are equal stand for equal meanings.
     */
    public static Optional<Boolean> recognizes(Object key, PatternMeaning meaning, String value) {
        return BUILT.computeIfAbsent(key, _ -> Optional.ofNullable(
                        of(meaning, PatternPlan.Budget.OF_A_FOLD.meter())))
                .flatMap(recognizer -> recognizer.accepts(value,
                        PatternPlan.Budget.OF_A_FOLD.meter()));
    }

    /** The recognizer for {@code meaning}, or null where building its machine would take more than
     *  {@code meter} allows. */
    public static Recognizer of(PatternMeaning meaning, Meter meter) {
        Automaton machine = Automaton.of(meaning, meter);
        return machine == null ? null : new Recognizer(machine);
    }

    /**
     * Whether the whole of {@code value} is one of the strings, or empty where walking it would look
     * at more than {@code meter} allows.
     *
     * <p>A walk reads each symbol once and is in every state the machine may be in, so what it
     * costs is the value's length times how many of those there are. The allowance is the
     * question's own, since one recognizer answers many of them.
     */
    public Optional<Boolean> accepts(String value, Meter meter) {
        return Optional.ofNullable(machine.accepts(value, meter));
    }
}
