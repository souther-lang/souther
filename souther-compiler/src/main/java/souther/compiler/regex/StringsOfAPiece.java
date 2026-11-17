package souther.compiler.regex;

import java.util.ArrayDeque;
import java.util.ArrayList;
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
 * Normalization Form C. The strings that have a piece in a language ({@link #wholesWithAPieceIn})
 * are told apart exactly: whether a string has a piece there is a question about that string, and
 * every string asked about is a value. The pieces of the values of a language
 * ({@link #pieceOfAValueAt}) are not the pieces of its strings, which are the pieces of strings no
 * value is as well: those of a string that is changed by normalization. They are answered only
 * where the two are the same, and not otherwise.
 *
 * <p>Where a {@code String} stops is no distinction a model made, so a piece is read as though a
 * string had no greatest length: a piece of a string held as written is the piece of a value
 * however long it is.
 */
public final class StringsOfAPiece {

    private StringsOfAPiece() {
    }

    /**
     * The pieces at {@code index} of the values of {@code whole} parted at {@code separator}, or
     * null where they are not worked out exactly: where making the machines for them is more than
     * {@code meter} allows, or where the pieces of the strings of the language are not those of the
     * strings it holds as written ({@link StringsHeldAsWritten}), a subset of its values, so that a
     * piece of some string of the language may be the piece of no value.
     *
     * <p>What the language holds of its strings that is no value is not told from here, so the
     * pieces of its strings are the pieces of its values only where the strings that are surely
     * values already have all of them. They are then both, and are all that is, without the
     * values being listed.
     */
    public static Language pieceOfAValueAt(Language whole, int separator, int index,
                                           Meter meter) {
        Shown shown = piecesOfValuesAt(whole, separator, index, meter);
        return shown != null && shown.all() ? shown.ofTheStrings() : null;
    }

    /**
     * The pieces at {@code index} of the values of {@code whole} parted at {@code separator}, as
     * far as each is shown to be one: no value has a piece outside {@link #ofTheStrings}, and
     * every string of {@link #ofTheValues} is the piece of a value.
     *
     * <p>Shown by writing the value out: a piece of a string held as written is the piece of that
     * string, which is a value.
     *
     * @param ofTheStrings the pieces of the strings of the language, which the pieces of its values
     *                     are among
     * @param ofTheValues  the pieces of the strings it holds as written, each of them the piece of a
     *                     value
     */
    public record Shown(Language ofTheStrings, Language ofTheValues) {

        public Shown {
            if (ofTheStrings == null || ofTheValues == null) {
                throw new IllegalArgumentException("pieces are shown of some strings");
            }
        }

        /** Whether every piece is shown one way or the other: the pieces of the strings are the
         *  pieces of the values. */
        public boolean all() {
            return ofTheStrings.equals(ofTheValues);
        }
    }

    /**
     * What is shown of the pieces at {@code index} of the values of {@code whole}
     * ({@link Shown}), or null where making the machines for them is more than {@code meter}
     * allows.
     */
    public static Shown piecesOfValuesAt(Language whole, int separator, int index, Meter meter) {
        return piecesOfValuesIn(whole, separator, index, index + 1L, meter);
    }

    /**
     * What is shown of the pieces of the values of {@code whole} at the indexes from {@code from}
     * up to, and not including, {@code until}, or to the last piece where {@code until} is below
     * nought ({@link Shown}), or null where making the machines for them is more than
     * {@code meter} allows. A string is among them when it is the piece at some index of the
     * window.
     */
    public static Shown piecesOfValuesIn(Language whole, int separator, long from, long until,
                                         Meter meter) {
        Language ofTheStrings = piecesIn(whole, separator, from, until, meter);
        if (ofTheStrings == null) {
            return null;
        }
        StringsInNormalFormC.Values values = StringsInNormalFormC.of(whole, meter);
        if (values == null) {
            return null;
        }
        // A piece is shown the piece of a value by writing a value out round it.
        Language written = values.surely();
        Language ofTheWritten = piecesIn(written, separator, from, until, meter);
        if (ofTheWritten == null) {
            return null;
        }
        return new Shown(ofTheStrings, ofTheWritten);
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
        return piecesIn(whole, separator, index, index + 1L, meter);
    }

    /**
     * The states of {@code machine} a piece begins in, at any index from {@code from} up to, and
     * not including, {@code until} — to the last where {@code until} is below nought — or null
     * where finding them is more than {@code making} allows, or an index they are found at is more
     * than an {@code int} holds.
     *
     * <p>A walk is in some states after passing a number of separators, and the states it is in
     * after the next one are fixed by those. Where they come round to a set they were before, the
     * indexes after that repeat, so an index far into a window costs a round and not itself.
     */
    private static BitSet beginningsIn(Automaton machine, int separator, long from,
                                       long until, Meter.Making making) {
        CodePoints within = CodePoints.of(separator).not();
        List<BitSet> after = new ArrayList<>();
        Map<BitSet, Integer> seen = new HashMap<>();
        BitSet begin = new BitSet();
        begin.set(Automaton.START);
        int cycleAt = -1;
        while (!begin.isEmpty()) {
            Integer before = seen.putIfAbsent(begin, after.size());
            if (before != null) {
                cycleAt = before;
                break;
            }
            after.add(begin);
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
        int counted = after.size();
        int period = cycleAt < 0 ? 0 : counted - cycleAt;
        long last = until < 0 ? Long.MAX_VALUE : until - 1;
        long through = Math.min(last, (cycleAt < 0 ? counted : Math.max(from, counted) + period) - 1L);
        if (through >= Integer.MAX_VALUE) {
            return null;
        }
        BitSet states = new BitSet();
        for (long index = from; index <= through; index++) {
            BitSet here = index < counted ? after.get((int) index)
                    : cycleAt < 0 ? new BitSet()
                    : after.get(cycleAt + (int) ((index - cycleAt) % period));
            states.or(here);
        }
        return states;
    }

    /**
     * The pieces at the indexes from {@code from} up to, and not including, {@code until} of the
     * strings of {@code whole} parted at {@code separator}, however long, or to the last piece
     * where {@code until} is below nought ({@link #piecesAt}); or null where making the machine
     * for them is more than {@code meter} allows.
     */
    static Language piecesIn(Language whole, int separator, long from, long until, Meter meter) {
        if (from < 0) {
            throw new IllegalArgumentException("a piece is at an index of nought or more: " + from);
        }
        Automaton machine = whole.machine();
        meter.starting();
        Meter.Making making = meter.making();
        CodePoints apart = CodePoints.of(separator);
        CodePoints within = apart.not();
        BitSet begin = beginningsIn(machine, separator, from, until, making);
        if (begin == null) {
            return null;
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
        return wholesWithAPieceInWindow(piece, separator, index, index + 1L, meter);
    }

    /**
     * The strings that have a piece in {@code piece} at some index from {@code from} up to, and not
     * including, {@code until} — to the last where {@code until} is below nought — when they are
     * parted at {@code separator}, or null where making the machine for them is more than
     * {@code meter} allows.
     *
     * <p>The walk passes {@code from} separators, then at each index of the window either reads a
     * piece of {@code piece} there and goes on as anything, or reads a piece that is none and
     * passes its separator to the next index, until the window's last index, where it must read
     * one.
     */
    public static Language wholesWithAPieceInWindow(Language piece, int separator, long from,
                                                    long until, Meter meter) {
        if (from < 0) {
            throw new IllegalArgumentException("a piece is at an index of nought or more: " + from);
        }
        Automaton machine = piece.machine();
        CodePoints apart = CodePoints.of(separator);
        CodePoints within = apart.not();
        int states = machine.size();
        boolean endless = until < 0;
        long stages = endless ? 1 : Math.max(0, until - from);
        meter.starting();
        if (stages == 0) {
            return Language.canonical(Automaton.madeOf(List.of(List.of()), new BitSet()), meter);
        }
        if (!meter.making().states(from + 2 * stages + states + 1)) {
            return null;
        }
        // States 0 to from - 1 are the walk before the window, one for each separator still to
        // pass. Then two states for each index of the window: at the start of a piece, and inside
        // one that is passed over. Then the machine of the piece, each state of it, and the last
        // state, which is the rest of the string after the piece, which is anything.
        int before = Math.toIntExact(from);
        int windowed = Math.toIntExact(stages);
        int started = before;
        int machines = started + 2 * windowed;
        int rest = machines + states;
        List<List<Automaton.Step>> steps = new ArrayList<>();
        BitSet accepting = new BitSet();
        for (int passed = 0; passed < before; passed++) {
            steps.add(List.of(new Automaton.Step(within, passed),
                    new Automaton.Step(apart, passed + 1)));
        }
        for (int stage = 0; stage < windowed; stage++) {
            boolean last = !endless && stage == windowed - 1;
            int atTheStart = started + 2 * stage;
            int inside = atTheStart + 1;
            int next = endless ? started : atTheStart + 2;
            List<Automaton.Step> opening = new ArrayList<>();
            for (Automaton.Step each : machine.stepsFrom(Automaton.START)) {
                CodePoints stays = each.over().and(within);
                if (!stays.isEmpty()) {
                    opening.add(new Automaton.Step(stays, machines + each.to()));
                }
            }
            if (machine.stopsAt(Automaton.START)) {
                opening.add(new Automaton.Step(apart, rest));
                accepting.set(atTheStart);
            }
            if (!last) {
                opening.add(new Automaton.Step(within, inside));
                opening.add(new Automaton.Step(apart, next));
            }
            steps.add(opening);
            steps.add(last ? List.of() : List.of(new Automaton.Step(within, inside),
                    new Automaton.Step(apart, next)));
        }
        for (int state = 0; state < states; state++) {
            List<Automaton.Step> out = new ArrayList<>();
            for (Automaton.Step each : machine.stepsFrom(state)) {
                CodePoints stays = each.over().and(within);
                if (!stays.isEmpty()) {
                    out.add(new Automaton.Step(stays, machines + each.to()));
                }
            }
            if (machine.stopsAt(state)) {
                out.add(new Automaton.Step(apart, rest));
                accepting.set(machines + state);
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
