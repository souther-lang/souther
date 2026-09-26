package souther.compiler.regex;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * The strings' own order, asked of a language.
 *
 * <p>Lexicographic over scalar values, which is the comparison the runtime makes and the one a
 * model's {@code <} is (spec §equality, {@code Strings.compare}). A symbol here is a scalar value
 * too, so the order of strings is the order of their symbols read one after another: a machine
 * steps over what the order compares, and both questions below are walks over a machine a symbol
 * at a time.
 *
 * <p><b>Answerable to the order itself.</b> Nothing here is a second definition of {@code <} on
 * strings: what is built is a machine and what is walked is a machine, and both are held to
 * {@code Strings.compare} by the laws over them
 * ({@code TheRuntimesOrderIsWhatTheseMachinesAnswerAboutTest}).
 */
final class RuntimeOrder {

    /**
     * The machine accepting every string that comes before {@code than}, or null past what
     * {@code meter} allows.
     *
     * <p>One state per symbol of {@code than} and two besides. A walk is at the state saying how
     * many of those symbols the string has matched exactly; a symbol below the next one settles the
     * answer and a symbol above it leads nowhere, so the states a walk can be in are that count, the
     * state where the whole of {@code than} has been matched, and the one where the answer is
     * already yes.
     *
     * <p>A walk that stops having matched some of {@code than} and no more is a string that is a
     * proper prefix of it, which is below it — so those states are where a walk may stop, and the
     * one that matched all of it is not, since that string is {@code than} itself.
     */
    static Automaton before(String than, Meter meter) {
        int[] symbols = than.codePoints().toArray();
        Meter.Making making = meter.making();
        if (!making.states(symbols.length + 2L)) {
            return null;
        }
        int below = symbols.length + 1;
        List<List<Automaton.Step>> steps = new ArrayList<>();
        for (int at = 0; at <= below; at++) {
            steps.add(new ArrayList<>());
        }
        BitSet accepting = new BitSet();
        for (int at = 0; at < symbols.length; at++) {
            accepting.set(at);
            CodePoints lower = CodePoints.below(symbols[at]);
            if (!lower.isEmpty()) {
                steps.get(at).add(new Automaton.Step(lower, below));
            }
            steps.get(at).add(new Automaton.Step(CodePoints.of(symbols[at]), at + 1));
        }
        accepting.set(below);
        steps.get(below).add(new Automaton.Step(CodePoints.EVERYTHING, below));
        return Automaton.madeOf(steps, accepting);
    }

    /**
     * Every string there is, canonical and made once.
     *
     * <p>A constant and not a construction a caller pays for. What it says is a fact about the
     * universe rather than anything a model wrote — charged to an allowance, every language would be
     * a little smaller than the one before it for a reason nobody could see.
     */
    static final Automaton EVERY_STRING = everyString();

    private static Automaton everyString() {
        List<List<Automaton.Step>> steps = new ArrayList<>();
        steps.add(new ArrayList<>(List.of(new Automaton.Step(CodePoints.EVERYTHING, 0))));
        BitSet accepting = new BitSet();
        accepting.set(0);
        Automaton one = Automaton.madeOf(steps, accepting).canonical(new Meter(16, 64));
        if (one == null) {
            throw new IllegalStateException("the machine for every string is one state");
        }
        return one;
    }

    /**
     * The least string {@code machine} accepts, or null where it accepts none and where the ones it
     * accepts have no least among them.
     *
     * <p>Two answers under one null on purpose: neither is a place on the order, and a caller
     * wanting them apart asks whether the language holds anything, which is free. What has no least
     * is a language whose strings descend without stopping — {@code a*b} holds {@code b} above
     * {@code ab} above {@code aab} and so on down — and the greatest lower bound of those is not a
     * string. There is nothing to write down, and a reading that answered with the one it had
     * reached would be naming a value the rules do not stop at.
     *
     * <p>Free, as everything asked of a language is: the machine is in front of this and nothing is
     * built. Asked of a canonical machine, which is deterministic, so a walk is in one state.
     *
     * <p>Least by taking the least symbol that still leads to somewhere a walk may stop, and
     * stopping at the first place it may. A shorter string is below every string it begins, so where
     * the walk may stop it has the least; and where it comes back to a state it has been in, it never
     * will — the same symbols are chosen again, and each time round leaves a string below the last.
     */
    static String leastOf(Automaton machine) {
        boolean[] reaches = machine.reachingSomewhereItStops();
        if (!reaches[Automaton.START]) {
            return null;
        }
        StringBuilder out = new StringBuilder();
        int here = Automaton.START;
        Set<Integer> been = new HashSet<>();
        while (been.add(here)) {
            if (machine.stopsAt(here)) {
                return out.toString();
            }
            Automaton.Step least = null;
            for (Automaton.Step step : machine.stepsFrom(here)) {
                if (reaches[step.to()] && (least == null
                        || step.over().least() < least.over().least())) {
                    least = step;
                }
            }
            if (least == null) {
                return null;
            }
            out.appendCodePoint(least.over().least());
            here = least.to();
        }
        return null;
    }

    private RuntimeOrder() {}
}
