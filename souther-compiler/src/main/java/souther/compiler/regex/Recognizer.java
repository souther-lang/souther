package souther.compiler.regex;

import java.util.Optional;
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
