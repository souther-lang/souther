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
 * The strings that are the piece at an index of some string of a language, and the strings that
 * have a piece at an index in a language, when the strings are parted at one code point.
 *
 * <p>The converse of {@link StringsByTheirPieces}, which says which whole strings have some piece,
 * or every piece, of a window in a language. Here the whole strings are the language and the
 * answer is the pieces: a string is the piece at {@code index} of some string of the language
 * exactly when the language holds a string that has it there. The pieces are the stretches
 * between separators, so a piece holds no separator, and a string with fewer pieces than
 * {@code index + 1} has none there.
 *
 * <p>Read off the machine of the language: the states a walk is in after {@code index}
 * separators, each reached through pieces that hold none, are where the piece begins, and it ends
 * where the string does or at a separator that the rest of some string of the language follows.
 */
public final class StringsOfAPiece {

    private StringsOfAPiece() {
    }

    /**
     * The pieces at {@code index} of the strings of {@code whole} parted at {@code separator}, or
     * null where making the machine for them is more than {@code meter} allows.
     */
    public static Language pieceAt(Language whole, int separator, int index, Meter meter) {
        if (index < 0) {
            throw new IllegalArgumentException("a piece is at an index of nought or more: " + index);
        }
        Automaton machine = whole.machine();
        CodePoints apart = CodePoints.of(separator);
        CodePoints within = apart.not();
        BitSet begin = new BitSet();
        begin.set(Automaton.START);
        for (int passed = 0; passed < index; passed++) {
            BitSet next = new BitSet();
            for (int state : withoutASeparator(machine, begin, within)) {
                for (Automaton.Step each : machine.stepsFrom(state)) {
                    if (each.over().has(separator)) {
                        next.set(each.to());
                    }
                }
            }
            begin = next;
        }
        boolean[] stopsAhead = machine.reachingSomewhereItStops();
        int states = machine.size();
        // State 0 begins the piece wherever a walk may, and state 1 + q is where the machine is
        // in state q partway through it.
        List<List<Automaton.Step>> steps = new ArrayList<>();
        BitSet accepting = new BitSet();
        List<Automaton.Step> opening = new ArrayList<>();
        for (int state = begin.nextSetBit(0); state >= 0; state = begin.nextSetBit(state + 1)) {
            opening.addAll(inThePiece(machine, state, within));
            if (endsThePiece(machine, state, apart, stopsAhead)) {
                accepting.set(0);
            }
        }
        steps.add(opening);
        for (int state = 0; state < states; state++) {
            steps.add(inThePiece(machine, state, within));
            if (endsThePiece(machine, state, apart, stopsAhead)) {
                accepting.set(1 + state);
            }
        }
        return Language.canonical(Automaton.madeOf(steps, accepting), meter);
    }

    /**
     * The strings that have a piece at {@code index}, when they are parted at {@code separator},
     * that is in {@code piece}, or null where making the machine for them is more than
     * {@code meter} allows.
     *
     * <p>The converse of {@link #pieceAt}: a walk passes {@code index} separators, each piece
     * before the one asked about any string without one, then reads a string of {@code piece} that
     * holds none, and the string ends there or goes on after a separator as anything.
     */
    public static Language wholesWithAPieceIn(Language piece, int separator, int index,
                                              Meter meter) {
        if (index < 0) {
            throw new IllegalArgumentException("a piece is at an index of nought or more: " + index);
        }
        Automaton machine = piece.machine();
        CodePoints apart = CodePoints.of(separator);
        CodePoints within = apart.not();
        int states = machine.size();
        // States 0 to index - 1 are the walk before the piece, one for each separator still to
        // pass. State index + q is the machine of the piece in state q, so the walk's last
        // separator leads to where the machine starts, and the last state is the rest of the
        // string after the piece, which is anything.
        int rest = index + states;
        List<List<Automaton.Step>> steps = new ArrayList<>();
        BitSet accepting = new BitSet();
        for (int passed = 0; passed < index; passed++) {
            steps.add(List.of(new Automaton.Step(within, passed),
                    new Automaton.Step(apart, passed + 1)));
        }
        for (int state = 0; state < states; state++) {
            List<Automaton.Step> out = new ArrayList<>();
            for (Automaton.Step each : machine.stepsFrom(state)) {
                CodePoints stays = each.over().and(within);
                if (!stays.isEmpty()) {
                    out.add(new Automaton.Step(stays, index + each.to()));
                }
            }
            if (machine.stopsAt(state)) {
                out.add(new Automaton.Step(apart, rest));
                accepting.set(index + state);
            }
            steps.add(out);
        }
        steps.add(List.of(new Automaton.Step(apart.or(within), rest)));
        accepting.set(rest);
        return Language.canonical(Automaton.madeOf(steps, accepting), meter);
    }

    /** The states a walk from {@code from} reaches on symbols other than the separator, those it
     *  starts in included. */
    private static List<Integer> withoutASeparator(Automaton machine, BitSet from,
                                                   CodePoints within) {
        BitSet seen = (BitSet) from.clone();
        Deque<Integer> pending = new ArrayDeque<>();
        for (int state = from.nextSetBit(0); state >= 0; state = from.nextSetBit(state + 1)) {
            pending.add(state);
        }
        List<Integer> out = new ArrayList<>();
        while (!pending.isEmpty()) {
            int state = pending.poll();
            out.add(state);
            for (Automaton.Step each : machine.stepsFrom(state)) {
                if (!each.over().and(within).isEmpty() && !seen.get(each.to())) {
                    seen.set(each.to());
                    pending.add(each.to());
                }
            }
        }
        return out;
    }

    /** The steps out of {@code state} that stay in a piece, moved on by the one state that
     *  begins the machine. */
    private static List<Automaton.Step> inThePiece(Automaton machine, int state,
                                                   CodePoints within) {
        List<Automaton.Step> out = new ArrayList<>();
        for (Automaton.Step each : machine.stepsFrom(state)) {
            CodePoints stays = each.over().and(within);
            if (!stays.isEmpty()) {
                out.add(new Automaton.Step(stays, 1 + each.to()));
            }
        }
        return out;
    }

    /** Whether a piece may end with the machine in {@code state}: the string ends there, or a
     *  separator follows and some string of the language is the rest. */
    private static boolean endsThePiece(Automaton machine, int state, CodePoints apart,
                                        boolean[] stopsAhead) {
        if (machine.stopsAt(state)) {
            return true;
        }
        for (Automaton.Step each : machine.stepsFrom(state)) {
            if (!each.over().and(apart).isEmpty() && stopsAhead[each.to()]) {
                return true;
            }
        }
        return false;
    }
}
