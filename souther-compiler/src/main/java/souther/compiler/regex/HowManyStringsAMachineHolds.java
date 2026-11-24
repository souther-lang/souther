package souther.compiler.regex;

import java.math.BigInteger;
import java.util.ArrayDeque;
import java.util.Deque;

import net.unit8.notation199x.pattern.Automaton;
import net.unit8.notation199x.pattern.CodePoints;

/**
 * How many strings one machine accepts, where they are finitely many.
 *
 * <p>A language's machine is canonical, so a string is accepted along one path and the strings are
 * the paths from the start to a state that stops: how many there are is the paths counted, each step
 * as many ways as the code points it reads. Only the states that can reach a stop are on a path
 * that ends, and where a loop is among them some string goes round it as often as it likes, so there
 * is no number of them.
 *
 * <p>Worked out over the states once, in the order the steps lead and with no recursion: a machine is
 * as deep as it has states, and what a count may cost is what the machine already cost to make.
 */
final class HowManyStringsAMachineHolds {

    private HowManyStringsAMachineHolds() {}

    /**
     * How many strings {@code machine} accepts, or null where it accepts endlessly many. Nought
     * where it accepts none.
     */
    static BigInteger of(Automaton machine) {
        boolean[] reaches = machine.reachingSomewhereItStops();
        if (!reaches[Automaton.START]) {
            return BigInteger.ZERO;
        }
        int states = machine.size();
        int[] leading = new int[states];
        for (int state = 0; state < states; state++) {
            if (!reaches[state]) {
                continue;
            }
            for (Automaton.Step step : machine.stepsFrom(state)) {
                if (reaches[step.to()]) {
                    leading[step.to()]++;
                }
            }
        }
        // The states no step of the others leads to are the ones a count can start from; taking
        // each away from those it leads to leaves a state with none only once all its own are
        // counted, so a state left over has a loop behind it.
        Deque<Integer> order = new ArrayDeque<>();
        for (int state = 0; state < states; state++) {
            if (reaches[state] && leading[state] == 0) {
                order.add(state);
            }
        }
        int[] inOrder = new int[states];
        int placed = 0;
        int onPaths = 0;
        for (boolean each : reaches) {
            onPaths += each ? 1 : 0;
        }
        while (!order.isEmpty()) {
            int here = order.poll();
            inOrder[placed++] = here;
            for (Automaton.Step step : machine.stepsFrom(here)) {
                if (reaches[step.to()] && --leading[step.to()] == 0) {
                    order.add(step.to());
                }
            }
        }
        if (placed < onPaths) {
            return null;
        }
        // From the last state a path can come to back to the first, so the strings of a state are
        // those of the states its steps lead to, each as many times as the code points it reads.
        BigInteger[] strings = new BigInteger[states];
        for (int at = placed - 1; at >= 0; at--) {
            int here = inOrder[at];
            BigInteger count = machine.stopsAt(here) ? BigInteger.ONE : BigInteger.ZERO;
            for (Automaton.Step step : machine.stepsFrom(here)) {
                if (reaches[step.to()]) {
                    count = count.add(howManyCodePoints(step.over()).multiply(strings[step.to()]));
                }
            }
            strings[here] = count;
        }
        return strings[Automaton.START];
    }

    private static BigInteger howManyCodePoints(CodePoints over) {
        BigInteger count = BigInteger.ZERO;
        for (var range : over.ranges()) {
            count = count.add(BigInteger.valueOf(range.to() - range.from() + 1L));
        }
        return count;
    }
}
