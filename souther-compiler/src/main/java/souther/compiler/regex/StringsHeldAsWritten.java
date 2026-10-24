package souther.compiler.regex;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;
import java.util.Map;

import net.unit8.notation199x.pattern.Automaton;
import net.unit8.notation199x.pattern.CodePoints;

/**
 * The strings of a language a {@code String} holds as they are written: every one of them is in
 * Normalization Form C, so the run time keeps each code point where the language put it, and each
 * is a value exactly as the language reads it.
 *
 * <p>What a language holds is sequences of code points, and a {@code String} holds a sequence only
 * as its Normalization Form C. A sequence the form changes is no value: {@code a} and a combining
 * acute are one code point held, and a language holding the two as two holds a string no value is.
 * So what is asked of the values a language leaves — that a code point stands somewhere, that
 * every number they come to is reached — is asked of these, every one of which is a value as
 * written ({@link StableStarters}). What every value is, a bound on them, is asked of the language
 * itself, which holds them all.
 *
 * <p>Its machine is the language's with every step kept to the stable starters, which is no larger
 * than the language's own: nothing here is built past what the language was built under.
 */
public final class StringsHeldAsWritten {

    private final Automaton machine;

    private StringsHeldAsWritten(Automaton machine) {
        this.machine = machine;
    }

    /** The strings of {@code language} held as written. The machine is a {@link Language}'s, which
     *  is canonical: deterministic, and every step of it takes a code point. */
    static StringsHeldAsWritten of(Automaton language) {
        List<List<Automaton.Step>> steps = new ArrayList<>();
        BitSet accepting = new BitSet();
        for (int state = 0; state < language.size(); state++) {
            List<Automaton.Step> kept = new ArrayList<>();
            for (Automaton.Step step : language.stepsFrom(state)) {
                CodePoints over = StableStarters.within(step.over());
                if (!over.isEmpty()) {
                    kept.add(new Automaton.Step(over, step.to()));
                }
            }
            steps.add(kept);
            accepting.set(state, language.stopsAt(state));
        }
        return new StringsHeldAsWritten(Automaton.madeOf(steps, accepting));
    }

    /**
     * Whether {@code value} is one of these: walked a code point at a time, each taking the one
     * step that holds it. The language's machine takes at most one step for a code point from a
     * state, and keeping its steps to fewer code points leaves it so. Asked by what checks these
     * against the values; a reading asks what they place and leave, below.
     */
    boolean has(String value) {
        int state = Automaton.START;
        for (int at = 0; at < value.length(); ) {
            int codePoint = value.codePointAt(at);
            int to = -1;
            for (Automaton.Step step : machine.stepsFrom(state)) {
                if (step.over().has(codePoint)) {
                    to = step.to();
                    break;
                }
            }
            if (to < 0) {
                return false;
            }
            state = to;
            at += Character.charCount(codePoint);
        }
        return machine.stopsAt(state);
    }

    /** The code points standing at {@code index} of these of {@code length} code points. */
    public CodePoints codePointsAt(int length, int index) {
        return CodePointRemainders.standingAt(machine, length, index);
    }

    /** {@link Language#alikeAt}, of these. */
    public List<CodePoints> alikeAt(int length, int index, CodePoints among) {
        return CodePointRemainders.alikeAt(machine, length, index, among);
    }

    /** {@link Language#remaindersLeft}, of these. */
    public BitSet remaindersLeft(int length, Map<Integer, Long> weights, long shift, int divisor,
                                 Map<Integer, CodePoints> at, int work) {
        return CodePointRemainders.left(machine, length, weights, shift, divisor, at, work);
    }
}
