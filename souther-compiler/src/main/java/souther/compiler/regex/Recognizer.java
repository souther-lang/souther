package souther.compiler.regex;

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

    private final Automaton machine;

    private Recognizer(Automaton machine) {
        this.machine = machine;
    }

    /** The recognizer for {@code meaning}, or null where building its machine would take more than
     *  {@code meter} allows. */
    public static Recognizer of(PatternMeaning meaning, Meter meter) {
        Automaton machine = Automaton.of(meaning, meter);
        return machine == null ? null : new Recognizer(machine);
    }

    /** Whether the whole of {@code value} is one of the strings. A walk that reads each symbol once. */
    public boolean accepts(String value) {
        return machine.accepts(value);
    }
}
