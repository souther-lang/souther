package souther.compiler.meaning;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Deque;
import java.util.List;

/**
 * A spelling of a proposition: a text, held as the pieces it was put together from rather than as
 * one string.
 *
 * <p>A proposition is spelled from the spellings of its parts, and those from theirs. Written out at
 * each level, every level holds again the whole text of everything below it, so a conjunction nested
 * {@code d} deep over parts of length {@code L} holds about {@code d·L + d²} characters, and a model
 * whose rules nest their comparisons holds gigabytes of the same few lines. Held as pieces, a
 * spelling holds its own few characters and a reference to each part's, so what is held is as large
 * as the propositions are and not as large as their texts written out.
 *
 * <p>It is the text all the same. Two spellings are equal exactly where their texts are, hash as
 * {@link String#hashCode} hashes the text, and are ordered as {@link String#compareTo} orders it —
 * worked out from the pieces, never by writing the text. The hash of a text put together is a
 * function of the hashes and lengths of its pieces; comparing walks both texts a piece at a time and
 * passes over a piece the two share whole, which is where two spellings of propositions built from
 * the same parts spend nearly all of their length.
 *
 * <p>{@link #toString} writes the text, for the places it is read; nothing that tells two apart or
 * puts them in order asks for it.
 */
public final class Spelling implements Comparable<Spelling> {


    /** What a list of parts' spellings is separated by, and closed by. */
    static final Spelling SEPARATOR = of(", ");
    static final Spelling CLOSE = of("]");

    /** What a spelling of a statement failing begins with, before the spelling of it holding. */
    private static final Spelling NOT = of("!");

    /** The text, where this is one piece; null where it is put together. */
    private final String text;
    /** What it is put together from, in order; empty where it is one piece. */
    private final List<Spelling> pieces;
    private final long length;
    /** {@link String#hashCode} of the text. */
    private final int hash;
    /** Thirty-one to the power of the length, as an {@code int} multiplies: what the hash of a
     *  text this one is followed by is multiplied by to put the two together. */
    private final int power;

    private Spelling(String text, List<Spelling> pieces, long length, int hash, int power) {
        this.text = text;
        this.pieces = pieces;
        this.length = length;
        this.hash = hash;
        this.power = power;
    }

    /** The spelling that is {@code text}. */
    public static Spelling of(String text) {
        return new Spelling(text, List.of(), text.length(), text.hashCode(), powerOf(text.length()));
    }

    /**
     * The spelling that is these written one after another: each a {@link Spelling}, or anything
     * else, which stands for its {@link String#valueOf}.
     */
    public static Spelling of(Object... written) {
        List<Spelling> pieces = new ArrayList<>(written.length);
        for (Object each : written) {
            pieces.add(each instanceof Spelling spelling ? spelling : of(String.valueOf(each)));
        }
        return joined(pieces);
    }

    /** {@code pieces} written one after another. */
    public static Spelling joined(List<Spelling> pieces) {
        if (pieces.size() == 1) {
            return pieces.getFirst();
        }
        long length = 0;
        int hash = 0;
        int power = 1;
        for (Spelling each : pieces) {
            length += each.length;
            hash = hash * each.power + each.hash;
            power *= each.power;
        }
        return new Spelling(null, List.copyOf(pieces), length, hash, power);
    }

    /**
     * The spelling of a statement that is {@code held} where it {@code holds}, and {@code !} before
     * it where it fails — with the spelling of it holding kept as the one piece after the mark, so
     * that turning it over ({@link #denied}) writes nothing again.
     */
    static Spelling denying(boolean holds, Spelling held) {
        return holds ? held : joined(List.of(NOT, held));
    }

    /** The other of the two spellings {@link #denying} makes of one statement, this being one. */
    Spelling denied() {
        return pieces.size() == 2 && pieces.getFirst() == NOT ? pieces.get(1) : denying(false, this);
    }

    /** Thirty-one to {@code exponent}, wrapping as an {@code int} multiplication wraps. */
    private static int powerOf(long exponent) {
        int result = 1;
        int base = 31;
        for (long left = exponent; left > 0; left >>= 1) {
            if ((left & 1) != 0) {
                result *= base;
            }
            base *= base;
        }
        return result;
    }

    /** How many {@code char}s the text is. */
    public long length() {
        return length;
    }

    @Override
    public int hashCode() {
        return hash;
    }

    @Override
    public boolean equals(Object other) {
        return this == other || (other instanceof Spelling that
                && length == that.length && hash == that.hash && compareTo(that) == 0);
    }

    /** As {@link String#compareTo} orders the two texts. */
    @Override
    public int compareTo(Spelling other) {
        if (this == other) {
            return 0;
        }
        Reading mine = new Reading(this);
        Reading theirs = new Reading(other);
        // A text that has ended where the other goes on is the first of the two, as String.compareTo
        // tells two texts apart by their lengths last.
        while (true) {
            boolean mineBetween = mine.atABoundary();
            boolean theirsBetween = theirs.atABoundary();
            if (mineBetween && theirsBetween) {
                Spelling here = mine.next();
                Spelling there = theirs.next();
                if (here == null || there == null) {
                    return byLength(other);
                }
                if (here == there) {
                    mine.pass();
                    theirs.pass();
                    continue;
                }
            }
            if (mineBetween) {
                if (mine.next() == null) {
                    return byLength(other);
                }
                mine.enter();
                continue;
            }
            if (theirsBetween) {
                if (theirs.next() == null) {
                    return byLength(other);
                }
                theirs.enter();
                continue;
            }
            int run = Math.min(mine.left(), theirs.left());
            for (int at = 0; at < run; at++) {
                char a = mine.text.charAt(mine.at + at);
                char b = theirs.text.charAt(theirs.at + at);
                if (a != b) {
                    return a - b;
                }
            }
            mine.at += run;
            theirs.at += run;
        }
    }

    /** What {@link String#compareTo} answers of two texts one of which begins the other: the
     *  difference of their lengths. */
    private int byLength(Spelling other) {
        return Math.clamp(length - other.length, Integer.MIN_VALUE, Integer.MAX_VALUE);
    }

    /**
     * A place in a spelling's text, walked a piece at a time with a stack of its own, so a spelling
     * as deep as its propositions are nested is read without the stack of the thread.
     */
    private static final class Reading {

        /** The pieces still to read, each with where in it the reading is. */
        private final Deque<int[]> places = new ArrayDeque<>();
        private final Deque<Spelling> of = new ArrayDeque<>();
        /** The text being read, and how far into it; null between pieces. */
        private String text;
        private int at;

        Reading(Spelling start) {
            of.push(start);
            places.push(new int[] {-1});
        }

        int left() {
            return text.length() - at;
        }

        /** Whether the reading stands between two pieces, at the start of the next one. */
        boolean atABoundary() {
            return text == null || at >= text.length();
        }

        /** The piece that starts here, or null where the text has ended. */
        Spelling next() {
            text = null;
            while (!of.isEmpty()) {
                int[] place = places.peek();
                Spelling node = of.peek();
                if (place[0] < 0) {
                    return node;
                }
                if (place[0] < node.pieces.size()) {
                    return node.pieces.get(place[0]);
                }
                // Read to its end. The piece it is in was passed when it was entered, so the place
                // below it stands at the piece after it already.
                of.pop();
                places.pop();
            }
            return null;
        }

        /** Past the piece that starts here, whole. */
        void pass() {
            int[] place = places.peek();
            if (place[0] < 0) {
                of.pop();
                places.pop();
            } else {
                place[0]++;
            }
        }

        /**
         * Into the piece that starts here, which there is: its text where it is one piece, which is
         * then what is read, and its own pieces where it is put together.
         */
        void enter() {
            Spelling node = next();
            pass();
            if (node.text != null) {
                text = node.text;
                at = 0;
                return;
            }
            of.push(node);
            places.push(new int[] {0});
        }
    }

    /** The text written out. */
    @Override
    public String toString() {
        if (text != null) {
            return text;
        }
        if (length > Integer.MAX_VALUE) {
            throw new IllegalStateException("a spelling of " + length + " chars has no String");
        }
        StringBuilder out = new StringBuilder((int) length);
        appendTo(out);
        return out.toString();
    }

    /** The text written onto the end of {@code out}. */
    public void appendTo(StringBuilder out) {
        Reading reading = new Reading(this);
        while (true) {
            if (reading.atABoundary()) {
                if (reading.next() == null) {
                    return;
                }
                reading.enter();
                continue;
            }
            out.append(reading.text, reading.at, reading.text.length());
            reading.at = reading.text.length();
        }
    }
}
