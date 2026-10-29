package souther.compiler.regex;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.BitSet;
import java.util.Deque;
import java.util.List;

import net.unit8.notation199x.pattern.Automaton;
import net.unit8.notation199x.pattern.CodePoints;
import net.unit8.notation199x.pattern.Meter;

/**
 * The strings that stand inside the strings of a language, and the strings that have some string
 * of a language inside them: the two sides of {@code String.contains}, {@code startsWith} and
 * {@code endsWith} when one string is left free and the other is a language.
 *
 * <p>Both are languages of the same machines that made the one asked about. A string stands
 * inside some string of a language exactly when it is read by the machine between two of its
 * states, so every state a string of the language can pass through is made a place to begin and a
 * place to stop; and a string has one of a language inside it exactly when the machine for that
 * language can be read where it stands, with anything before it and anything after it. Which of
 * the two ends the string may have beyond the one inside is the {@link Where}.
 */
public final class StringsInsideStrings {

    private StringsInsideStrings() {
    }

    /** Where the inner string stands in the outer one. */
    public enum Where {

        /** Anywhere in it. */
        ANYWHERE,

        /** At the start of it, which is a prefix. */
        AT_THE_START,

        /** At the end of it, which is a suffix. */
        AT_THE_END
    }

    /**
     * Every string that stands where {@code where} says in some string of {@code outer}, or null
     * past what {@code meter} allows. The empty string stands in every string, so it is among them
     * wherever {@code outer} holds one.
     */
    public static Language standingIn(Language outer, Where where, Meter meter) {
        Automaton machine = outer.machine();
        boolean[] trim = trimStates(machine);
        int states = machine.size();
        if (!trim[Automaton.START]) {
            return Language.canonical(Automaton.madeOf(List.of(List.of()), new BitSet()), meter);
        }
        BitSet accepting = new BitSet();
        List<List<Automaton.Step>> steps = new ArrayList<>();
        switch (where) {
            case AT_THE_START -> {
                // The prefixes: the machine itself, stopped at any state a string passes through.
                for (int state = 0; state < states; state++) {
                    steps.add(trim[state] ? stepsWithin(machine, state, trim, 0) : List.of());
                    accepting.set(state, trim[state]);
                }
            }
            case ANYWHERE, AT_THE_END -> {
                // Begun at any state a string passes through: state 0 begins where any of them
                // does, and state 1 + q is the machine at q.
                List<Automaton.Step> opening = new ArrayList<>();
                steps.add(opening);
                for (int state = 0; state < states; state++) {
                    steps.add(trim[state] ? stepsWithin(machine, state, trim, 1) : List.of());
                    if (trim[state]) {
                        opening.addAll(stepsWithin(machine, state, trim, 1));
                    }
                }
                accepting.set(0);
                for (int state = 0; state < states; state++) {
                    accepting.set(1 + state, trim[state]
                            && (where == Where.ANYWHERE || machine.stopsAt(state)));
                }
            }
        }
        return Language.canonical(Automaton.madeOf(steps, accepting), meter);
    }

    /**
     * Every string that has some string of {@code inner} inside it where {@code where} says, or
     * null past what {@code meter} allows.
     */
    public static Language havingInside(Language inner, Where where, Meter meter) {
        Automaton machine = inner.machine();
        int states = machine.size();
        CodePoints any = CodePoints.EVERYTHING;
        BitSet accepting = new BitSet();
        List<List<Automaton.Step>> steps = new ArrayList<>();
        switch (where) {
            case AT_THE_START -> {
                // The machine, then anything: from where a string of it stops, anything goes on.
                int rest = states;
                for (int state = 0; state < states; state++) {
                    List<Automaton.Step> out = new ArrayList<>(machine.stepsFrom(state));
                    if (machine.stopsAt(state)) {
                        out.add(new Automaton.Step(any, rest));
                        accepting.set(state);
                    }
                    steps.add(out);
                }
                steps.add(List.of(new Automaton.Step(any, rest)));
                accepting.set(rest);
            }
            case ANYWHERE, AT_THE_END -> {
                // Anything first, then the machine from its start: state 0 is the anything, state
                // 1 + q the machine at q, and the last state anything after a string has stopped.
                int rest = 1 + states;
                List<Automaton.Step> opening = new ArrayList<>();
                opening.add(new Automaton.Step(any, 0));
                for (Automaton.Step each : machine.stepsFrom(Automaton.START)) {
                    opening.add(new Automaton.Step(each.over(), 1 + each.to()));
                }
                steps.add(opening);
                for (int state = 0; state < states; state++) {
                    List<Automaton.Step> out = new ArrayList<>();
                    for (Automaton.Step each : machine.stepsFrom(state)) {
                        out.add(new Automaton.Step(each.over(), 1 + each.to()));
                    }
                    if (machine.stopsAt(state)) {
                        accepting.set(1 + state);
                        if (where == Where.ANYWHERE) {
                            out.add(new Automaton.Step(any, rest));
                        }
                    }
                    steps.add(out);
                }
                if (where == Where.ANYWHERE) {
                    steps.add(List.of(new Automaton.Step(any, rest)));
                    accepting.set(rest);
                } else {
                    steps.add(List.of());
                }
                if (machine.stopsAt(Automaton.START)) {
                    accepting.set(0);
                    if (where == Where.ANYWHERE) {
                        opening.add(new Automaton.Step(any, rest));
                    }
                }
            }
        }
        return Language.canonical(Automaton.madeOf(steps, accepting), meter);
    }

    /** The states a string of the machine passes through: reached from where it starts, and
     *  with a string of it to go on to. */
    private static boolean[] trimStates(Automaton machine) {
        int states = machine.size();
        boolean[] reached = new boolean[states];
        Deque<Integer> pending = new ArrayDeque<>();
        reached[Automaton.START] = true;
        pending.add(Automaton.START);
        while (!pending.isEmpty()) {
            int state = pending.poll();
            for (Automaton.Step each : machine.stepsFrom(state)) {
                if (!reached[each.to()]) {
                    reached[each.to()] = true;
                    pending.add(each.to());
                }
            }
        }
        boolean[] stops = machine.reachingSomewhereItStops();
        boolean[] out = new boolean[states];
        for (int state = 0; state < states; state++) {
            out[state] = reached[state] && stops[state];
        }
        return out;
    }

    /** The steps out of {@code state} that lead to a state a string passes through, moved on by
     *  {@code shift} states. */
    private static List<Automaton.Step> stepsWithin(Automaton machine, int state, boolean[] trim,
                                                    int shift) {
        List<Automaton.Step> out = new ArrayList<>();
        for (Automaton.Step each : machine.stepsFrom(state)) {
            if (trim[each.to()]) {
                out.add(new Automaton.Step(each.over(), shift + each.to()));
            }
        }
        return out;
    }
}
