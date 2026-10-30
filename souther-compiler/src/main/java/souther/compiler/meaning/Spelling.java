package souther.compiler.meaning;

import souther.compiler.collect.HeldOnce;

import java.util.ArrayDeque;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Deque;
import java.util.IdentityHashMap;
import java.util.List;
import java.util.Set;

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
 *
 * <p><b>A text a {@code String} can be, and no longer.</b> What a spelling is equal to and ordered by
 * is a {@code String}'s, and the hash and the order are a {@code String}'s only for a text one could
 * hold. Held as pieces a spelling can be made far longer than that from a few objects — a piece
 * written twice, twice over, is a text of four — and a length past what is counted wraps, past which
 * a text of every length is the empty one to its hash and its length alike. So a spelling longer than
 * a {@code String} holds is not made: what a proposition comes to written out is held to a budget
 * where it is concluded and where it is put together, and a spelling past this is a budget that was
 * not asked, which is said where it happens rather than read as another text.
 */
public final class Spelling implements Comparable<Spelling> {

    /**
     * The spellings of one piece made last. The same few texts are spelled over and over — the
     * name of a place, a word between two parts — and each spelling made of one was held with a
     * copy of the text of its own for as long as what it spells.
     */
    private static final HeldOnce<Spelling> WRITTEN = new HeldOnce<>(14);

    /** What a list of parts' spellings is separated by, and closed by. */
    static final Spelling SEPARATOR = of(", ");
    static final Spelling CLOSE = of("]");

    /** What a spelling of a statement failing begins with, before the spelling of it holding. */
    private static final Spelling NOT = of("!");

    /** The text, where this is one piece; null where it is put together. */
    private final String text;
    /** What it is put together from, in order; empty where it is one piece. */
    private final List<Spelling> pieces;
    /** How many {@code char}s the text is, which a {@code String} could hold. */
    private final int length;
    /** {@link String#hashCode} of the text. */
    private final int hash;
    /** Thirty-one to the power of the length, as an {@code int} multiplies: what the hash of a
     *  text this one is followed by is multiplied by to put the two together. */
    private final int power;

    private Spelling(String text, List<Spelling> pieces, int length, int hash, int power) {
        this.text = text;
        this.pieces = pieces;
        this.length = length;
        this.hash = hash;
        this.power = power;
    }

    /** The spelling that is {@code text}. */
    public static Spelling of(String text) {
        return WRITTEN.held(new Spelling(text, List.of(), text.length(), text.hashCode(),
                powerOf(text.length())));
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

    /**
     * {@code pieces} written one after another.
     *
     * @throws IllegalArgumentException where the text they come to is longer than a {@code String}
     *                                  holds, which no spelling is
     */
    public static Spelling joined(List<Spelling> pieces) {
        if (pieces.size() == 1) {
            return pieces.getFirst();
        }
        // Each length is at most what an int holds and there are at most as many pieces, so the
        // sum is held by a long whatever they are.
        long length = 0;
        int hash = 0;
        int power = 1;
        for (Spelling each : pieces) {
            length += each.length;
            hash = hash * each.power + each.hash;
            power *= each.power;
        }
        if (length > Integer.MAX_VALUE) {
            throw new IllegalArgumentException("a spelling of " + length + " chars is longer than a"
                    + " String holds; what put it together was held to no budget");
        }
        return new Spelling(null, List.copyOf(pieces), (int) length, hash, power);
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
    private static int powerOf(int exponent) {
        int result = 1;
        int base = 31;
        for (int left = exponent; left > 0; left >>= 1) {
            if ((left & 1) != 0) {
                result *= base;
            }
            base *= base;
        }
        return result;
    }

    /** Whether {@code piece} itself is held somewhere among the pieces this is put together from,
     *  however deep — each piece looked at once, however many times it is held. */
    public boolean holdsWithin(Spelling piece) {
        Set<Spelling> seen = Collections.newSetFromMap(new IdentityHashMap<>());
        Deque<Spelling> left = new ArrayDeque<>(pieces);
        while (!left.isEmpty()) {
            Spelling each = left.pop();
            if (each == piece) {
                return true;
            }
            if (seen.add(each)) {
                each.pieces.forEach(left::push);
            }
        }
        return false;
    }

    /** How many {@code char}s the text is. */
    public int length() {
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
        if (text != null && other.text != null) {
            return text.compareTo(other.text);
        }
        // Nearly every pair differs within the first piece of text each begins with, which is found
        // without a reading of either: the piece every first piece down to a text starts.
        String mineFirst = firstText();
        String theirsFirst = other.firstText();
        int common = Math.min(mineFirst.length(), theirsFirst.length());
        for (int at = 0; at < common; at++) {
            char a = mineFirst.charAt(at);
            char b = theirsFirst.charAt(at);
            if (a != b) {
                return a - b;
            }
        }
        Reading[] both = READINGS.get();
        Reading mine = both[0].from(this);
        Reading theirs = both[1].from(other);
        try {
            return compareRead(mine, theirs, other);
        } finally {
            mine.clear();
            theirs.clear();
        }
    }

    /**
     * The two readings each thread compares with, made once and read again from the start of each
     * pair it is asked of: an order is asked of every pair a sorted table files, and readings made
     * for each would be as many objects again as the pairs.
     */
    private static final ThreadLocal<Reading[]> READINGS =
            ThreadLocal.withInitial(() -> new Reading[] {new Reading(), new Reading()});

    /** {@link #compareTo}, read from the start of both texts, {@code mine} being this one's. */
    private int compareRead(Reading mine, Reading theirs, Spelling other) {
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

    /** The text of the piece the whole text starts with, found down the first piece of each; empty
     *  where that piece is empty, which then says nothing of what follows it. */
    private String firstText() {
        Spelling at = this;
        while (at.text == null) {
            if (at.pieces.isEmpty()) {
                return "";
            }
            at = at.pieces.getFirst();
        }
        return at.text;
    }

    /** What {@link String#compareTo} answers of two texts one of which begins the other: the
     *  difference of their lengths, which two lengths of a String's differ by in an int. */
    private int byLength(Spelling other) {
        return length - other.length;
    }

    /**
     * A place in a spelling's text, walked a piece at a time with a stack of its own, so a spelling
     * as deep as its propositions are nested is read without the stack of the thread — two arrays
     * that grow as deep as the deepest reading has gone, so a reading made again goes as deep with
     * nothing made.
     */
    private static final class Reading {

        /** The pieces still to read, innermost last, and where in each the reading is: before the
         *  piece itself where that is the start, and at one of its own pieces otherwise. */
        private Spelling[] of = new Spelling[16];
        private int[] places = new int[16];
        private int depth;
        /** The text being read, and how far into it; null between pieces. */
        private String text;
        private int at;

        /** This reading, at the start of {@code start}. */
        Reading from(Spelling start) {
            push(start, -1);
            return this;
        }

        /** Nothing read and nothing held, so a reading kept for the next pair keeps no text alive. */
        void clear() {
            Arrays.fill(of, 0, depth, null);
            depth = 0;
            text = null;
            at = 0;
        }

        private void push(Spelling node, int place) {
            if (depth == of.length) {
                of = Arrays.copyOf(of, depth * 2);
                places = Arrays.copyOf(places, depth * 2);
            }
            of[depth] = node;
            places[depth] = place;
            depth++;
        }

        private void pop() {
            depth--;
            of[depth] = null;
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
            while (depth > 0) {
                int place = places[depth - 1];
                Spelling node = of[depth - 1];
                if (place < 0) {
                    return node;
                }
                if (place < node.pieces.size()) {
                    return node.pieces.get(place);
                }
                // Read to its end. The piece it is in was passed when it was entered, so the place
                // below it stands at the piece after it already.
                pop();
            }
            return null;
        }

        /** Past the piece that starts here, whole. */
        void pass() {
            if (places[depth - 1] < 0) {
                pop();
            } else {
                places[depth - 1]++;
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
            push(node, 0);
        }
    }

    /** The text written out. */
    @Override
    public String toString() {
        if (text != null) {
            return text;
        }
        StringBuilder out = new StringBuilder(length);
        appendTo(out);
        return out.toString();
    }

    /** The text written onto the end of {@code out}. */
    public void appendTo(StringBuilder out) {
        Reading reading = new Reading().from(this);
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
