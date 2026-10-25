package souther.compiler.regex;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Deque;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

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

    /**
     * Whether there are none of these.
     *
     * <p>Only a non-empty answer is evidence: one of these is a value. A language holding a
     * string made of code points that are not stable starters may hold a value too, so an empty
     * answer here does not say that no value exists.
     */
    public boolean isEmpty() {
        BitSet reached = new BitSet();
        Deque<Integer> pending = new ArrayDeque<>();
        reached.set(Automaton.START);
        pending.add(Automaton.START);
        while (!pending.isEmpty()) {
            int state = pending.poll();
            if (machine.stopsAt(state)) {
                return false;
            }
            for (Automaton.Step step : machine.stepsFrom(state)) {
                if (!reached.get(step.to())) {
                    reached.set(step.to());
                    pending.add(step.to());
                }
            }
        }
        return true;
    }

    /**
     * Whether these have a string of every length {@code language} has one: a length of the
     * language is a length some value has.
     *
     * <p>Both machines are walked a code point at a time with the states they can be in, which is
     * a unary automaton of each, and the walk ends when the pair of state sets repeats. That is a
     * decision when it ends, and a refusal to answer when it does not end within
     * {@link #LAYERS}: false then says the equality was not shown.
     */
    boolean hasEveryLengthOf(Automaton language) {
        BitSet inLanguage = new BitSet();
        BitSet inThese = new BitSet();
        inLanguage.set(Automaton.START);
        inThese.set(Automaton.START);
        Set<List<BitSet>> seen = new HashSet<>();
        for (int layer = 0; layer < LAYERS; layer++) {
            if (stopsIn(language, inLanguage) != stopsIn(machine, inThese)) {
                return false;
            }
            if (!seen.add(List.of(inLanguage, inThese))) {
                return true;
            }
            inLanguage = after(language, inLanguage);
            inThese = after(machine, inThese);
        }
        return false;
    }

    /** The layers {@link #hasEveryLengthOf} walks before it gives up. */
    private static final int LAYERS = 4096;

    private static boolean stopsIn(Automaton automaton, BitSet states) {
        for (int state = states.nextSetBit(0); state >= 0; state = states.nextSetBit(state + 1)) {
            if (automaton.stopsAt(state)) {
                return true;
            }
        }
        return false;
    }

    private static BitSet after(Automaton automaton, BitSet states) {
        BitSet next = new BitSet();
        for (int state = states.nextSetBit(0); state >= 0; state = states.nextSetBit(state + 1)) {
            for (Automaton.Step step : automaton.stepsFrom(state)) {
                next.set(step.to());
            }
        }
        return next;
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
