package souther.compiler.regex;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.BitSet;
import java.util.Deque;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import net.unit8.notation199x.pattern.Automaton;
import net.unit8.notation199x.pattern.CodePoints;
import net.unit8.notation199x.pattern.Meter;
import souther.runtime.Strings;

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
 *
 * <p>A language holds sequences of code points, and a {@code String} holds only those in
 * Normalization Form C that are no longer than {@link Strings#LONGEST_TEXT}. The strings that have
 * a piece in a language ({@link #wholesWithAPieceIn}) are told apart exactly: whether a string has
 * a piece there is a question about that string, and every string asked about is a value. The
 * pieces of the values of a language ({@link #pieceOfAValueAt}) are not the pieces of its strings,
 * which are the pieces of strings no value is as well: one of a string that is changed by
 * normalization, or one near the longest string, which is longer than any piece by the stretches
 * round it. They are answered only where the two are the same, and not otherwise.
 */
public final class StringsOfAPiece {

    private StringsOfAPiece() {
    }

    /**
     * The pieces at {@code index} of the values of {@code whole} parted at {@code separator}, of
     * up to {@code longest} code points, or null where they are not worked out exactly: where
     * making the machines for them is more than {@code meter} allows, where a piece of that length
     * is not shown to be that of a string a {@code String} holds ({@link Shown#upTo}), or where
     * the pieces of the strings of the language are not those of the strings it holds as written
     * ({@link StringsHeldAsWritten}), a subset of its values, so that a piece of some string of the
     * language may be the piece of no value.
     *
     * <p>What the language holds of its strings that is no value is not told from here, so the
     * pieces of its strings are the pieces of its values only where the strings that are surely
     * values already have all of them. They are then both, and are all that is, without the
     * values being listed.
     */
    public static Language pieceOfAValueAt(Language whole, int separator, int index,
                                           long longest, Meter meter) {
        Shown shown = piecesOfValuesAt(whole, separator, index, meter);
        return shown != null && shown.allUpTo(longest) ? shown.ofTheStrings() : null;
    }

    /**
     * The pieces at {@code index} of the values of {@code whole} parted at {@code separator}, as
     * far as each is shown to be one: no value has a piece outside {@link #ofTheStrings}, and
     * every string of {@link #ofTheValues} no longer than {@link #upTo} is the piece of a value.
     *
     * <p>Shown by writing the value out. A piece of a string held as written is put between the
     * shortest stretch that brings the machine to where the piece begins and the shortest that
     * takes it on from where the piece ends to the end of some string, and the longest of those two
     * together is what a piece gives up of the longest string. A piece longer than that may still
     * be the piece of a value, and nothing here says whether it is.
     *
     * @param ofTheStrings the pieces of the strings of the language, which the pieces of its values
     *                     are among
     * @param ofTheValues  the pieces of the strings it holds as written, each of them the piece of a
     *                     value where it is short enough
     * @param upTo         the most code points a piece of {@code ofTheValues} is shown to be the
     *                     piece of a value at; below nought where none is
     */
    public record Shown(Language ofTheStrings, Language ofTheValues, long upTo) {

        public Shown {
            if (ofTheStrings == null || ofTheValues == null) {
                throw new IllegalArgumentException("pieces are shown of some strings");
            }
        }

        /** Whether every piece of up to {@code longest} code points is shown one way or the
         *  other: the pieces of the strings are the pieces of the values, and are as long. */
        public boolean allUpTo(long longest) {
            return longest <= upTo && ofTheStrings.equals(ofTheValues);
        }
    }

    /**
     * What is shown of the pieces at {@code index} of the values of {@code whole}
     * ({@link Shown}), or null where making the machines for them is more than {@code meter}
     * allows.
     */
    public static Shown piecesOfValuesAt(Language whole, int separator, int index, Meter meter) {
        Language ofTheStrings = piecesAt(whole, separator, index, meter);
        if (ofTheStrings == null) {
            return null;
        }
        Language written = whole.heldAsWritten().language(meter);
        if (written == null) {
            return null;
        }
        Language ofTheWritten = piecesAt(written, separator, index, meter);
        if (ofTheWritten == null) {
            return null;
        }
        long around = mostAround(written.machine(), separator, index);
        return new Shown(ofTheStrings, ofTheWritten, Strings.LONGEST_TEXT - around);
    }

    /**
     * The most code points a string of {@code machine} needs round a piece at {@code index} for
     * the piece to stand there: the shortest stretch to each state a piece begins in, and the
     * shortest from each state a piece reached from it ends in, the most of the two together.
     *
     * <p>Walked separator by separator where the index is no more than the machine's states, and
     * otherwise bounded by {@code (index + 2) * (states + 1)}: from any state a machine reaches any
     * other it can reach in fewer than {@code states} symbols, so the stretch before each
     * separator, the separator, and the rest after the piece come to no more than that. Either way
     * a string that has the piece there at all has one no longer than the piece and this.
     */
    static long mostAround(Automaton machine, int separator, int index) {
        int states = machine.size();
        if (index > states) {
            return (index + 2L) * (states + 1L);
        }
        CodePoints apart = CodePoints.of(separator);
        CodePoints within = apart.not();
        long[] before = new long[states];
        Arrays.fill(before, Long.MAX_VALUE);
        before[Automaton.START] = 0;
        for (int passed = 0; passed < index; passed++) {
            long[] through = shortestWithin(machine, before, within);
            long[] next = new long[states];
            Arrays.fill(next, Long.MAX_VALUE);
            for (int state = 0; state < states; state++) {
                if (through[state] == Long.MAX_VALUE) {
                    continue;
                }
                for (Automaton.Step each : machine.stepsFrom(state)) {
                    if (!each.over().and(apart).isEmpty()) {
                        next[each.to()] = Math.min(next[each.to()], through[state] + 1);
                    }
                }
            }
            before = next;
        }
        long[] toAnEnd = shortestToAnEnd(machine);
        long most = 0;
        for (int begin = 0; begin < states; begin++) {
            if (before[begin] == Long.MAX_VALUE) {
                continue;
            }
            long[] from = new long[states];
            Arrays.fill(from, Long.MAX_VALUE);
            from[begin] = 0;
            long[] inThePiece = shortestWithin(machine, from, within);
            for (int end = 0; end < states; end++) {
                if (inThePiece[end] == Long.MAX_VALUE) {
                    continue;
                }
                long after = afterAPieceEndingAt(machine, end, apart, toAnEnd);
                if (after != Long.MAX_VALUE) {
                    most = Math.max(most, before[begin] + after);
                }
            }
        }
        return most;
    }

    /** The fewest code points from where {@code from} has each state to each state reached on
     *  symbols other than the separator. */
    private static long[] shortestWithin(Automaton machine, long[] from, CodePoints within) {
        long[] out = from.clone();
        Deque<Integer> pending = new ArrayDeque<>();
        for (int state = 0; state < out.length; state++) {
            if (out[state] != Long.MAX_VALUE) {
                pending.add(state);
            }
        }
        while (!pending.isEmpty()) {
            int state = pending.poll();
            for (Automaton.Step each : machine.stepsFrom(state)) {
                if (!each.over().and(within).isEmpty() && out[state] + 1 < out[each.to()]) {
                    out[each.to()] = out[state] + 1;
                    pending.add(each.to());
                }
            }
        }
        return out;
    }

    /** The fewest code points from each state to the end of some string, or
     *  {@link Long#MAX_VALUE} from a state no string ends past. */
    private static long[] shortestToAnEnd(Automaton machine) {
        int states = machine.size();
        List<List<Integer>> into = new ArrayList<>();
        for (int state = 0; state < states; state++) {
            into.add(new ArrayList<>());
        }
        for (int state = 0; state < states; state++) {
            for (Automaton.Step each : machine.stepsFrom(state)) {
                into.get(each.to()).add(state);
            }
        }
        long[] out = new long[states];
        Arrays.fill(out, Long.MAX_VALUE);
        Deque<Integer> pending = new ArrayDeque<>();
        for (int state = 0; state < states; state++) {
            if (machine.stopsAt(state)) {
                out[state] = 0;
                pending.add(state);
            }
        }
        while (!pending.isEmpty()) {
            int state = pending.poll();
            for (int earlier : into.get(state)) {
                if (out[earlier] == Long.MAX_VALUE) {
                    out[earlier] = out[state] + 1;
                    pending.add(earlier);
                }
            }
        }
        return out;
    }

    /** The fewest code points after a piece that leaves the machine in {@code state}: none where
     *  a string ends there, and otherwise a separator and the shortest rest of some string, or
     *  {@link Long#MAX_VALUE} where a piece cannot end there. */
    private static long afterAPieceEndingAt(Automaton machine, int state, CodePoints apart,
                                            long[] toAnEnd) {
        if (machine.stopsAt(state)) {
            return 0;
        }
        long out = Long.MAX_VALUE;
        for (Automaton.Step each : machine.stepsFrom(state)) {
            if (!each.over().and(apart).isEmpty() && toAnEnd[each.to()] != Long.MAX_VALUE) {
                out = Math.min(out, 1 + toAnEnd[each.to()]);
            }
        }
        return out;
    }

    /**
     * Whether every piece at {@code index} that a string of a machine of {@code states} states
     * has, of up to {@code longest} code points, is the piece of a string a {@code String} holds.
     *
     * <p>From any state a machine reaches any other it can reach in fewer than {@code states}
     * symbols, so the stretch before each of the {@code index} separators, the separator, and the
     * rest after the piece come to no more than {@code (index + 2) * (states + 1)} code points
     * beyond the piece. A string that has the piece there at all has one that short.
     */
    static boolean fitsAString(int index, int states, long longest) {
        return longest >= 0 && longest <= Strings.LONGEST_TEXT
                && (index + 2L) * (states + 1L) <= Strings.LONGEST_TEXT - longest;
    }

    /**
     * The pieces at {@code index} of the strings of {@code whole} parted at {@code separator}, as
     * far as the pieces of up to {@code longest} code points go: the language holds the longer
     * ones, and says nothing true of them. Null where making the machine for them is more than
     * {@code meter} allows, and where a piece of that length may be the piece of no string a
     * {@code String} holds ({@link #fitsAString}) — which is wherever the caller cannot say its
     * pieces are shorter than the longest string by the stretches round them.
     */
    static Language pieceAt(Language whole, int separator, int index, long longest,
                                   Meter meter) {
        if (!fitsAString(index, whole.machine().size(), longest)) {
            return null;
        }
        return piecesAt(whole, separator, index, meter);
    }

    /**
     * The pieces at {@code index} of the strings of {@code whole} parted at {@code separator},
     * however long: a piece of a string of the language is among them, and one of them is the piece
     * of some string of the language, which may be longer than any a {@code String} holds. Null
     * where making the machine for them is more than {@code meter} allows.
     */
    static Language piecesAt(Language whole, int separator, int index, Meter meter) {
        if (index < 0) {
            throw new IllegalArgumentException("a piece is at an index of nought or more: " + index);
        }
        Automaton machine = whole.machine();
        meter.starting();
        Meter.Making making = meter.making();
        CodePoints apart = CodePoints.of(separator);
        CodePoints within = apart.not();
        BitSet begin = new BitSet();
        begin.set(Automaton.START);
        // Where the states a walk begins a piece in come round to a set they were before, the
        // passes left are those of one round, so a large index costs a round and not itself.
        Map<BitSet, Integer> seen = new HashMap<>();
        int limit = index;
        for (int passed = 0; passed < limit && !begin.isEmpty(); passed++) {
            Integer before = seen.put(begin, passed);
            if (before != null) {
                limit = passed + (index - passed) % (passed - before);
                seen.clear();
                if (passed >= limit) {
                    break;
                }
            }
            if (!making.work(machine.size())) {
                return null;
            }
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
        meter.starting();
        if (!meter.making().states((long) index + states + 1)) {
            return null;
        }
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
