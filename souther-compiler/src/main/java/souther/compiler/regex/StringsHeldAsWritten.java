package souther.compiler.regex;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Collections;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.WeakHashMap;
import java.util.function.IntPredicate;

import net.unit8.notation199x.pattern.Automaton;
import net.unit8.notation199x.pattern.CodePoints;
import net.unit8.notation199x.pattern.Meter;

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

    /**
     * What has been made, for the machine it was made of. A function of the machine alone, asked by
     * every reading of a string position, each of which would otherwise walk every step of the
     * machine through {@link StableStarters} again.
     *
     * <p>Kept here and not on {@link Language}: a language is held by the answers the store keeps,
     * and a field on it would put one more object that compares by address under every one of them.
     * Keyed by the machine itself, which compares by address, and held weakly so that an entry goes
     * with its machine.
     */
    private static final Map<Automaton, StringsHeldAsWritten> MADE =
            Collections.synchronizedMap(new WeakHashMap<>());

    /** The strings of {@code language} held as written. The machine is a {@link Language}'s, which
     *  is canonical: deterministic, and every step of it takes a code point. Two threads that ask
     *  first make two equal values and keep one. */
    static StringsHeldAsWritten of(Automaton language) {
        StringsHeldAsWritten had = MADE.get(language);
        if (had == null) {
            had = made(language);
            StringsHeldAsWritten raced = MADE.putIfAbsent(language, had);
            if (raced != null) {
                had = raced;
            }
        }
        return had;
    }

    private static StringsHeldAsWritten made(Automaton language) {
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

    /** These as a language, or null past what {@code meter} allows. */
    Language language(Meter meter) {
        return Language.canonical(machine, meter);
    }

    /**
     * Whether there are none of these.
     *
     * <p>Only a non-empty answer is evidence: one of these is a value. A language holding a
     * string made of code points that are not stable starters may hold a value too, so an empty
     * answer here does not say that no value exists.
     */
    public boolean isEmpty() {
        return shortestIn(machine) < 0;
    }

    /**
     * The fewest code points one of the strings of {@code language} held as written has, or -1
     * where it holds none, without making their machine: the language's walked a layer at a time
     * from its start, a step taken where it holds a stable starter, to the first state that
     * stops. The machine of these keeps every such code point of every step, so it is the same
     * walk.
     */
    static long shortestIn(Automaton language) {
        BitSet reached = new BitSet();
        Deque<Integer> layer = new ArrayDeque<>();
        reached.set(Automaton.START);
        layer.add(Automaton.START);
        for (long length = 0; !layer.isEmpty(); length++) {
            Deque<Integer> next = new ArrayDeque<>();
            for (int state : layer) {
                if (language.stopsAt(state)) {
                    return length;
                }
                for (Automaton.Step step : language.stepsFrom(state)) {
                    if (!reached.get(step.to()) && StableStarters.anyWithin(step.over())) {
                        reached.set(step.to());
                        next.add(step.to());
                    }
                }
            }
            layer = next;
        }
        return -1;
    }

    /**
     * Whether these have a string of every length {@code wanted} names.
     *
     * <p>The machine is walked a code point at a time with the states it can be in, which is a
     * unary automaton of it. {@code wanted} names the lengths of one stretch. Where {@code
     * endless}, the stretch has no end, so the walk ends at the first set of states it meets again
     * and every layer of the cycle must stop; otherwise it ends at the first layer past the
     * stretch. A walk that does not end within {@link #LAYERS} is a refusal to answer: false then
     * says only that it was not shown.
     */
    boolean reachesEveryLength(IntPredicate wanted, boolean endless) {
        BitSet states = new BitSet();
        states.set(Automaton.START);
        Map<BitSet, Integer> metAt = new HashMap<>();
        List<Boolean> stops = new ArrayList<>();
        boolean inStretch = false;
        for (int layer = 0; layer < LAYERS; layer++) {
            boolean stopsHere = stopsIn(machine, states);
            boolean named = wanted.test(layer);
            if (named && !stopsHere) {
                return false;
            }
            if (!endless && inStretch && !named) {
                return true;
            }
            inStretch |= named;
            stops.add(stopsHere);
            Integer before = endless ? metAt.putIfAbsent(states, layer) : null;
            if (before != null) {
                return stops.subList(before, layer).stream().allMatch(stop -> stop);
            }
            states = after(machine, states);
        }
        return false;
    }

    /** The layers {@link #reachesEveryLength} walks before it gives up. */
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
