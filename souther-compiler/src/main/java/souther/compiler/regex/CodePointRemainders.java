package souther.compiler.regex;

import java.util.ArrayList;
import java.util.BitSet;
import java.util.List;
import java.util.Map;

import net.unit8.notation199x.pattern.Automaton;
import net.unit8.notation199x.pattern.CodePoints;

/**
 * What a weighed total of the code points of a machine's strings of one length leaves divided by a
 * number, walked over the machine itself.
 *
 * <p>A layer of the walk is, at each state, the remainders a walk of so many symbols reaches it
 * with, and a step moves each of them by its index's weight times every code point of the step,
 * taken by the divisor. A run of code points a divisor long moves a remainder by every multiple
 * the weight leaves, so a step is walked over at most a divisor's worth of its code points however
 * many it holds. Only states a walk of the length from the start reaches and that reach a state
 * the machine stops at in the steps left are walked: which code points stand together at the
 * indices is the machine's, and nothing here takes the indices apart.
 */
final class CodePointRemainders {

    private CodePointRemainders() {
    }

    /**
     * The remainders {@code shift} and the code points of a string {@code machine} accepts of
     * {@code length} code points, each weighed by what {@code weights} has for its index, leave
     * divided by {@code divisor} — with the code point at each index {@code at} names one of those
     * it names. Null where working it out would take more than {@code work} remainders moved.
     */
    static BitSet left(Automaton machine, int length, Map<Integer, Long> weights, long shift,
                       int divisor, Map<Integer, CodePoints> at, int work) {
        boolean[][] onTheWay = onTheWay(machine, length, at);
        int states = machine.size();
        BitSet[] here = new BitSet[states];
        BitSet left = new BitSet(divisor);
        if (!onTheWay[0][Automaton.START]) {
            return left;
        }
        here[Automaton.START] = new BitSet(divisor);
        here[Automaton.START].set(Math.floorMod(shift, divisor));
        // Counted wide, and asked of what is left before it is spent, so a large step neither
        // passes the work unnoticed nor wraps round below it.
        long spent = 0;
        for (int index = 0; index < length; index++) {
            long weight = Math.floorMod(weights.getOrDefault(index, 0L), divisor);
            BitSet[] next = new BitSet[states];
            for (int state = 0; state < states; state++) {
                if (here[state] == null) {
                    continue;
                }
                for (Automaton.Step step : machine.stepsFrom(state)) {
                    CodePoints over = step.over().and(at.getOrDefault(index, CodePoints.EVERYTHING));
                    if (!onTheWay[index + 1][step.to()] || over.isEmpty()) {
                        continue;
                    }
                    BitSet moves = movesOf(over, weight, divisor);
                    long cost = (long) here[state].cardinality() * moves.cardinality() + divisor;
                    if (cost > work - spent) {
                        return null;
                    }
                    spent += cost;
                    BitSet reached = next[step.to()] == null ? new BitSet(divisor)
                            : next[step.to()];
                    for (int from = here[state].nextSetBit(0); from >= 0;
                         from = here[state].nextSetBit(from + 1)) {
                        for (int by = moves.nextSetBit(0); by >= 0; by = moves.nextSetBit(by + 1)) {
                            reached.set((int) (((long) from + by) % divisor));
                        }
                    }
                    next[step.to()] = reached;
                }
            }
            here = next;
        }
        for (int state = 0; state < states; state++) {
            if (here[state] != null && machine.stopsAt(state)) {
                left.or(here[state]);
            }
        }
        return left;
    }

    /** The code points that stand at {@code index} of a string {@code machine} accepts of
     *  {@code length} code points. */
    static CodePoints standingAt(Automaton machine, int length, int index) {
        boolean[][] onTheWay = onTheWay(machine, length, Map.of());
        CodePoints out = CodePoints.NONE;
        for (int state = 0; state < machine.size(); state++) {
            if (!onTheWay[index][state]) {
                continue;
            }
            for (Automaton.Step step : machine.stepsFrom(state)) {
                if (onTheWay[index + 1][step.to()]) {
                    out = out.or(step.over());
                }
            }
        }
        return out;
    }

    /**
     * {@code among} taken apart into the sets of code points every one of which the steps at
     * {@code index} of a walk of {@code length} take alike: each is taken by the same steps, so a
     * string holding one of them at the index is a string holding any other there, and what the
     * rest of the string comes to is the same for each.
     */
    static List<CodePoints> alikeAt(Automaton machine, int length, int index, CodePoints among) {
        boolean[][] onTheWay = onTheWay(machine, length, Map.of());
        List<CodePoints> out = new ArrayList<>(List.of(among));
        for (int state = 0; state < machine.size(); state++) {
            if (!onTheWay[index][state]) {
                continue;
            }
            for (Automaton.Step step : machine.stepsFrom(state)) {
                if (!onTheWay[index + 1][step.to()]) {
                    continue;
                }
                List<CodePoints> split = new ArrayList<>();
                for (CodePoints each : out) {
                    for (CodePoints part : List.of(each.and(step.over()), each.less(step.over()))) {
                        if (!part.isEmpty()) {
                            split.add(part);
                        }
                    }
                }
                out = split;
            }
        }
        return List.copyOf(out);
    }

    /**
     * For each index from nought to {@code length}, the states a walk of that many code points
     * from the start reaches that a walk of the rest reaches a state the machine stops at from —
     * each code point one {@code at} allows at its index.
     */
    private static boolean[][] onTheWay(Automaton machine, int length,
                                        Map<Integer, CodePoints> at) {
        int states = machine.size();
        boolean[][] from = new boolean[length + 1][states];
        from[0][Automaton.START] = true;
        for (int index = 0; index < length; index++) {
            for (int state = 0; state < states; state++) {
                if (!from[index][state]) {
                    continue;
                }
                for (Automaton.Step step : machine.stepsFrom(state)) {
                    if (!step.over().and(at.getOrDefault(index, CodePoints.EVERYTHING)).isEmpty()) {
                        from[index + 1][step.to()] = true;
                    }
                }
            }
        }
        boolean[][] onTheWay = new boolean[length + 1][states];
        for (int state = 0; state < states; state++) {
            onTheWay[length][state] = from[length][state] && machine.stopsAt(state);
        }
        for (int index = length - 1; index >= 0; index--) {
            for (int state = 0; state < states; state++) {
                if (!from[index][state]) {
                    continue;
                }
                for (Automaton.Step step : machine.stepsFrom(state)) {
                    if (onTheWay[index + 1][step.to()] && !step.over()
                            .and(at.getOrDefault(index, CodePoints.EVERYTHING)).isEmpty()) {
                        onTheWay[index][state] = true;
                        break;
                    }
                }
            }
        }
        return onTheWay;
    }

    /** What a code point of {@code over} weighed by {@code weight} moves a remainder by, taken by
     *  {@code divisor}. */
    private static BitSet movesOf(CodePoints over, long weight, int divisor) {
        BitSet moves = new BitSet(divisor);
        for (var run : over.ranges()) {
            long last = Math.min(run.to(), (long) run.from() + divisor - 1);
            for (long codePoint = run.from(); codePoint <= last; codePoint++) {
                moves.set((int) (weight * Math.floorMod(codePoint, divisor) % divisor));
            }
        }
        return moves;
    }
}
