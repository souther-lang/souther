package souther.runtime;

import org.jspecify.annotations.Nullable;

import java.lang.invoke.MethodHandles;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.function.Predicate;

/**
 * The strings a pattern of the language accepts, as a machine a run walks. Backs
 * {@code String.matches} and a decoder's format constraint.
 *
 * <p>No pattern text is here and none is read. The compiler reads a pattern, builds the machine it
 * means, and writes the machine into the class as an image ({@link Writer}); what a class loads is
 * that image, through {@link #read}. So nothing at run time decides what a pattern means, and no
 * engine's way of finding a match is involved in the answer.
 *
 * <p>A walk reads each character of the subject once, holds no stack and never goes back. Where the
 * machine is deterministic a character is one lookup; where it is not, a character moves each state
 * the walk is in, and a state is in the walk at most once. Which of the two an image holds is the
 * compiler's choice and changes no answer: a pattern whose deterministic machine is too large to
 * write is written as the machine its shape builds, which is never larger than the pattern's
 * repetitions written out.
 *
 * <p>A symbol is a scalar value. Text holding half a surrogate pair is no {@code String}, and no set
 * in an image holds a surrogate, so such text is accepted by nothing.
 */
public final class StringPattern implements Predicate<String> {

    /**
     * The most characters one string of an image holds.
     *
     * <p>A string of an image is a constant of the class it is written into, and a class file holds a
     * constant string in at most this many bytes (JVMS 4.4.7). An image is written in ASCII, which
     * is one byte a character.
     */
    public static final int CHUNK = 65_535;

    private final boolean deterministic;

    /** For each state, whether the walk may stop there. */
    private final boolean[] accepting;

    /** For each state, whether a walk from it can still reach one it may stop at. A walk left with
     *  none of those has its answer already. */
    private final boolean[] live;

    /**
     * For each state of a deterministic machine, its steps as runs sorted by where they begin:
     * {@code from, to, target} for each. For a machine that is not deterministic, empty.
     */
    private final int[][] runs;

    /** For each state of a machine that is not deterministic, the sets its steps are over, as
     *  {@code from, to} pairs. */
    private final int[][][] over;

    /** Where each of those steps leads. */
    private final int[][] target;

    /** For each state, the states a walk is also in for no character. */
    private final int[][] free;

    /**
     * The most entries an {@link Ascii} table holds. A deterministic machine whose table would be
     * larger walks every character by its runs.
     *
     * <p>The table is held for as long as the class holding the pattern, beside the image it was
     * read from. The machines an invariant writes take a few hundred entries.
     */
    private static final int MOST_ASCII_ENTRIES = 1 << 16;

    /** Where an ASCII character leads from each state of a deterministic machine, or null where
     *  there is no such table. */
    private final @Nullable Ascii ascii;

    private StringPattern(boolean deterministic, boolean[] accepting, int[][] runs,
                          int[][][] over, int[][] target, int[][] free) {
        this.deterministic = deterministic;
        this.accepting = accepting;
        this.runs = runs;
        this.over = over;
        this.target = target;
        this.free = free;
        this.live = live(accepting, target, free);
        this.ascii = deterministic ? ascii(runs, live) : null;
    }

    /**
     * A deterministic machine's steps over ASCII, one lookup a character.
     *
     * <p>Most text a pattern is asked about is ASCII, and a run over it is otherwise a search over a
     * state's runs for every character, which for a class such as {@code \w} or {@code .} is several
     * comparisons. The characters are put into kinds first: two characters no run tells apart step
     * every state to the same state, so the table is as wide as the kinds and not as the characters.
     *
     * @param kind  for each ASCII character, the kind it is in
     * @param kinds how many kinds there are
     * @param steps for each state and kind, at {@code state * kinds + kind}, the state it leads to,
     *              or -1 where it leads nowhere or to a state from which no walk is accepted
     */
    private record Ascii(byte[] kind, int kinds, int[] steps) {}

    /** The {@link Ascii} table of a deterministic machine, or null where it would hold more than
     *  {@link #MOST_ASCII_ENTRIES}. */
    private static @Nullable Ascii ascii(int[][] runs, boolean[] live) {
        // A kind begins at 0 and wherever a run begins or ends inside ASCII.
        boolean[] begins = new boolean[ASCII + 1];
        begins[0] = true;
        for (int[] each : runs) {
            for (int at = 0; at < each.length; at += 3) {
                if (each[at] < ASCII) {
                    begins[each[at]] = true;
                }
                if (each[at + 1] + 1 < ASCII) {
                    begins[each[at + 1] + 1] = true;
                }
            }
        }
        byte[] kind = new byte[ASCII];
        int kinds = 0;
        for (int c = 0; c < ASCII; c++) {
            if (begins[c]) {
                kinds++;
            }
            kind[c] = (byte) (kinds - 1);
        }
        if ((long) runs.length * kinds > MOST_ASCII_ENTRIES) {
            return null;
        }
        // Each kind is asked by its first character, which steps every state as the rest of it does.
        int[] first = new int[kinds];
        for (int c = ASCII - 1; c >= 0; c--) {
            first[kind[c]] = c;
        }
        int[] steps = new int[runs.length * kinds];
        for (int state = 0; state < runs.length; state++) {
            for (int each = 0; each < kinds; each++) {
                int to = next(runs[state], first[each]);
                steps[state * kinds + each] = (to >= 0 && live[to]) ? to : -1;
            }
        }
        return new Ascii(kind, kinds, steps);
    }

    /** How many characters ASCII is. */
    private static final int ASCII = 128;

    /** Whether the whole of {@code value} is one of the strings. */
    public boolean matches(String value) {
        return deterministic ? walk(value) : spread(value);
    }

    @Override
    public boolean test(String value) {
        return matches(value);
    }

    /**
     * The pattern an image writes, for a class loading the constant it was written as.
     *
     * <p>The bootstrap of that constant. The class holds the image as the strings it was cut into,
     * and the JVM resolves the constant once and answers from its pool afterwards.
     */
    public static StringPattern read(MethodHandles.Lookup lookup, String name, Class<?> type,
                                     String... image) {
        return of(List.of(image));
    }

    /** The pattern {@code image} writes. */
    public static StringPattern of(List<String> image) {
        Ints in = new Ints(String.join("", image));
        boolean deterministic = in.next() == 1;
        int[][] sets = new int[in.next()][];
        for (int i = 0; i < sets.length; i++) {
            int[] ranges = new int[in.next() * 2];
            for (int at = 0; at < ranges.length; at++) {
                ranges[at] = in.next();
            }
            sets[i] = ranges;
        }
        int states = in.next();
        boolean[] accepting = new boolean[states];
        int[][][] over = new int[states][][];
        int[][] target = new int[states][];
        int[][] free = new int[states][];
        for (int state = 0; state < states; state++) {
            accepting[state] = in.next() == 1;
            int steps = in.next();
            over[state] = new int[steps][];
            target[state] = new int[steps];
            for (int step = 0; step < steps; step++) {
                over[state][step] = sets[in.next()];
                target[state][step] = in.next();
            }
            free[state] = new int[in.next()];
            for (int at = 0; at < free[state].length; at++) {
                free[state][at] = in.next();
            }
            if (deterministic && free[state].length > 0) {
                throw new IllegalArgumentException(
                        "a deterministic machine steps nowhere for no character");
            }
        }
        if (!in.done()) {
            throw new IllegalArgumentException("an image holds one machine and nothing after it");
        }
        int[][] runs = deterministic ? runs(over, target) : new int[0][];
        return new StringPattern(deterministic, accepting, runs, over, target, free);
    }

    /** A deterministic machine's steps as sorted runs, so a character is one search. */
    private static int[][] runs(int[][][] over, int[][] target) {
        int[][] out = new int[over.length][];
        for (int state = 0; state < over.length; state++) {
            List<int[]> each = new ArrayList<>();
            for (int step = 0; step < over[state].length; step++) {
                int[] ranges = over[state][step];
                for (int at = 0; at < ranges.length; at += 2) {
                    each.add(new int[] {ranges[at], ranges[at + 1], target[state][step]});
                }
            }
            each.sort((one, other) -> Integer.compare(one[0], other[0]));
            int[] flat = new int[each.size() * 3];
            for (int i = 0; i < each.size(); i++) {
                System.arraycopy(each.get(i), 0, flat, i * 3, 3);
            }
            out[state] = flat;
        }
        return out;
    }

    /** Which states reach one a walk may stop at, walked back from those. */
    private static boolean[] live(boolean[] accepting, int[][] target, int[][] free) {
        int states = accepting.length;
        List<List<Integer>> back = new ArrayList<>(states);
        for (int state = 0; state < states; state++) {
            back.add(new ArrayList<>());
        }
        for (int state = 0; state < states; state++) {
            for (int to : target[state]) {
                back.get(to).add(state);
            }
            for (int to : free[state]) {
                back.get(to).add(state);
            }
        }
        boolean[] out = new boolean[states];
        int[] waiting = new int[states];
        int count = 0;
        for (int state = 0; state < states; state++) {
            if (accepting[state]) {
                out[state] = true;
                waiting[count++] = state;
            }
        }
        while (count > 0) {
            for (int from : back.get(waiting[--count])) {
                if (!out[from]) {
                    out[from] = true;
                    waiting[count++] = from;
                }
            }
        }
        return out;
    }

    /**
     * One state at a time, over a machine that is deterministic.
     *
     * <p>An ASCII character is one lookup in the {@link Ascii} table where the machine has one, and
     * every other character a search of the state's runs. The table leads nowhere rather than to a
     * state no walk is accepted from, so a walk stops at the same character either way.
     */
    private boolean walk(String value) {
        @Nullable Ascii table = ascii;
        int state = 0;
        int at = 0;
        int length = value.length();
        while (at < length) {
            char unit = value.charAt(at);
            if (table != null && unit < ASCII) {
                state = table.steps()[state * table.kinds() + table.kind()[unit]];
                at++;
            } else {
                if (!live[state]) {
                    return false;
                }
                int symbol = value.codePointAt(at);
                at += Character.charCount(symbol);
                state = next(runs[state], symbol);
            }
            if (state < 0) {
                return false;
            }
        }
        return accepting[state];
    }

    /** Where {@code symbol} leads from a state whose runs are {@code runs}, or -1 where it leads
     *  nowhere. */
    private static int next(int[] runs, int symbol) {
        int low = 0;
        int high = runs.length / 3 - 1;
        while (low <= high) {
            int mid = (low + high) >>> 1;
            if (runs[mid * 3 + 1] < symbol) {
                low = mid + 1;
            } else if (runs[mid * 3] > symbol) {
                high = mid - 1;
            } else {
                return runs[mid * 3 + 2];
            }
        }
        return -1;
    }

    /**
     * Every state the walk is in at once, over a machine that is not deterministic.
     *
     * <p>A state is put in the walk once for each character however many ways lead to it, which is
     * what keeps a character's work to the machine's size: {@code seen} holds the character a state
     * was last put in for.
     */
    private boolean spread(String value) {
        int states = accepting.length;
        int[] here = new int[states];
        int[] there = new int[states];
        int[] seen = new int[states];
        int[] pending = new int[states];
        int round = 1;
        int count = close(0, here, 0, seen, round, pending);
        int at = 0;
        while (at < value.length()) {
            if (count == 0) {
                return false;
            }
            int symbol = value.codePointAt(at);
            at += Character.charCount(symbol);
            round++;
            int next = 0;
            for (int i = 0; i < count; i++) {
                int state = here[i];
                int[][] sets = over[state];
                for (int step = 0; step < sets.length; step++) {
                    if (holds(sets[step], symbol)) {
                        next = close(target[state][step], there, next, seen, round, pending);
                    }
                }
            }
            int[] was = here;
            here = there;
            there = was;
            count = next;
        }
        for (int i = 0; i < count; i++) {
            if (accepting[here[i]]) {
                return true;
            }
        }
        return false;
    }

    /** {@code from} and every state it reaches for no character, put into {@code into} after its
     *  first {@code count}; answers how many it holds now. */
    private int close(int from, int[] into, int count, int[] seen, int round, int[] pending) {
        if (seen[from] == round || !live[from]) {
            return count;
        }
        seen[from] = round;
        int top = 0;
        pending[top++] = from;
        int held = count;
        while (top > 0) {
            int state = pending[--top];
            into[held++] = state;
            for (int to : free[state]) {
                if (seen[to] != round && live[to]) {
                    seen[to] = round;
                    pending[top++] = to;
                }
            }
        }
        return held;
    }

    /** Whether {@code symbol} is in a set held as ascending {@code from, to} pairs. */
    private static boolean holds(int[] ranges, int symbol) {
        int low = 0;
        int high = ranges.length / 2 - 1;
        while (low <= high) {
            int mid = (low + high) >>> 1;
            if (ranges[mid * 2 + 1] < symbol) {
                low = mid + 1;
            } else if (ranges[mid * 2] > symbol) {
                high = mid - 1;
            } else {
                return true;
            }
        }
        return false;
    }

    /**
     * An image being written, by a compiler holding a machine.
     *
     * <p>Here beside the reader, so the one format has one owner: a writer in the compiler and a
     * reader here would be two accounts of it, and nothing would hold them to each other.
     *
     * <p>A set is written once however many steps are over it. The machine a pattern's shape builds
     * writes a repetition out as copies, and each copy steps over the same set, so a class written
     * large is not written again for every copy.
     *
     * <p>Bounded as it is written and not after. Every state, step and set added counts the
     * characters it comes to in the image, and a writer past its limit says so ({@link #holds}) so
     * that whoever is writing stops there, rather than an image being made whole and then found too
     * large. Counted exactly, but for the two counts at the front, which are taken at their widest:
     * a limit counted loosely would refuse machines the image holds.
     */
    public static final class Writer {

        private final boolean deterministic;
        private final long mostCharacters;
        private long characters;
        private final List<String> sets = new ArrayList<>();
        private final Map<String, Integer> known = new HashMap<>();
        private final List<Boolean> accepting = new ArrayList<>();
        private final List<List<int[]>> steps = new ArrayList<>();
        private final List<List<Integer>> free = new ArrayList<>();

        /**
         * @param deterministic  whether the machine is only ever in one state, and so steps nowhere
         *                       for no character
         * @param mostCharacters the most characters the image may take
         */
        public Writer(boolean deterministic, long mostCharacters) {
            this.deterministic = deterministic;
            this.mostCharacters = mostCharacters;
            // The kind, and the two counts written before what they count, at their widest.
            this.characters = 2 + 2 * NUMBER;
        }

        /** The most characters one number of an image takes, its comma included. */
        private static final int NUMBER = 11;

        /** The characters {@code value} is written in, its comma included. */
        private static int written(int value) {
            return Integer.toString(value).length() + 1;
        }

        /** Whether what has been added so far still fits the image's limit. */
        public boolean holds() {
            return characters <= mostCharacters;
        }

        /**
         * The set {@code ranges} holds, as ascending {@code from, to} pairs, named by the number a
         * step refers to it by.
         */
        public int set(int[] ranges) {
            if (ranges.length % 2 != 0) {
                throw new IllegalArgumentException("a set is written as pairs");
            }
            StringBuilder out = new StringBuilder();
            out.append(ranges.length / 2);
            for (int each : ranges) {
                out.append(',').append(each);
            }
            String written = out.toString();
            Integer had = known.get(written);
            if (had != null) {
                return had;
            }
            sets.add(written);
            known.put(written, sets.size() - 1);
            characters += written.length() + 1;
            return sets.size() - 1;
        }

        /** One more state, numbered from nought in the order they are asked for; the first is where
         *  a walk begins. */
        public int state(boolean stops) {
            accepting.add(stops);
            steps.add(new ArrayList<>());
            free.add(new ArrayList<>());
            // Whether it stops, and its two counts while they are nought.
            characters += 6;
            return accepting.size() - 1;
        }

        /** A step from {@code from} over the set numbered {@code set}, to {@code to}. */
        public void step(int from, int set, int to) {
            List<int[]> out = steps.get(from);
            out.add(new int[] {set, to});
            characters += written(set) + written(to) + grown(out.size());
        }

        /** The character a count takes on where it has just grown by a digit. */
        private static int grown(int count) {
            return written(count) - written(count - 1);
        }

        /** A step from {@code from} to {@code to} that takes no character. */
        public void free(int from, int to) {
            if (deterministic) {
                throw new IllegalArgumentException(
                        "a deterministic machine steps nowhere for no character");
            }
            List<Integer> out = free.get(from);
            out.add(to);
            characters += written(to) + grown(out.size());
        }

        /** The image, cut into strings a class can hold ({@link #CHUNK}). Asked of a writer that
         *  {@link #holds}. */
        public List<String> image() {
            if (!holds()) {
                throw new IllegalStateException("an image past its limit is not written out");
            }
            StringBuilder out = new StringBuilder();
            out.append(deterministic ? 1 : 0).append(',').append(sets.size());
            for (String each : sets) {
                out.append(',').append(each);
            }
            out.append(',').append(accepting.size());
            for (int state = 0; state < accepting.size(); state++) {
                out.append(',').append(accepting.get(state) ? 1 : 0);
                out.append(',').append(steps.get(state).size());
                for (int[] step : steps.get(state)) {
                    out.append(',').append(step[0]).append(',').append(step[1]);
                }
                out.append(',').append(free.get(state).size());
                for (int to : free.get(state)) {
                    out.append(',').append(to);
                }
            }
            List<String> chunks = new ArrayList<>();
            for (int at = 0; at < out.length(); at += CHUNK) {
                chunks.add(out.substring(at, Math.min(out.length(), at + CHUNK)));
            }
            return List.copyOf(chunks);
        }
    }

    /** The numbers of an image, read in order. */
    private static final class Ints {

        private final String text;
        private int at;

        Ints(String text) {
            this.text = text;
        }

        int next() {
            if (at >= text.length()) {
                throw new IllegalArgumentException("an image ends before its machine does");
            }
            int value = 0;
            int start = at;
            while (at < text.length() && text.charAt(at) != ',') {
                char digit = text.charAt(at++);
                if (digit < '0' || digit > '9') {
                    throw new IllegalArgumentException("an image is written in numbers: " + digit);
                }
                value = Math.addExact(Math.multiplyExact(value, 10), digit - '0');
            }
            if (at == start) {
                throw new IllegalArgumentException("an image writes no empty number");
            }
            at++;
            return value;
        }

        boolean done() {
            return at >= text.length();
        }
    }

    @Override
    public String toString() {
        return (deterministic ? "a deterministic machine of " : "a machine of ")
                + accepting.length + " states";
    }
}
