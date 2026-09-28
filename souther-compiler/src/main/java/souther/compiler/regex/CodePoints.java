package souther.compiler.regex;

import java.util.ArrayList;
import java.util.List;

/**
 * A set of the characters a string is made of: Unicode scalar values, every code point but the
 * surrogates.
 *
 * <p>The universe is what a {@code String} can hold (spec §string-code-points), and not what a Java
 * matcher could be handed. A matcher reads half of a surrogate pair as a symbol of its own, but no
 * {@code String} holds one — text is let in only once it is a sequence of scalar values — so a
 * surrogate is no symbol here, and nothing made of these can name one: a range is never allowed to
 * hold one, and the complement is taken within the scalar values. That is what lets every sequence
 * of symbols a machine here reads be a string.
 *
 * <p>Held as ranges, sorted and disjoint and never touching. Two spellings of one set would make
 * equal sets unequal, and what is written out of a reading has to come out the same on two compiles
 * of one model — so the constructor normalises rather than trusting whoever built it.
 *
 * <p>The operations are the whole of what a character class is. A literal is one code point, a class
 * is a union of ranges, a negated class is the universe less that union, and {@code .} is the
 * universe less the five line terminators. None of them is a rule of its own here: they are all the
 * same algebra, which is what stops a reader having to know which shape a set came from.
 */
public record CodePoints(List<Range> ranges) {

    /** The greatest symbol there is. */
    public static final int LAST = 0x10FFFF;

    /** The first and the last surrogate, which are not symbols: the hole in the scalar values. */
    private static final int SURROGATES_FROM = 0xD800;
    private static final int SURROGATES_TO = 0xDFFF;

    /**
     * One run of symbols, both ends in it.
     *
     * <p>Never over a surrogate. A run that would span the hole is two runs, which is what
     * {@link #between} makes of it.
     */
    public record Range(int from, int to) {

        public Range {
            if (from < 0 || to > LAST || from > to) {
                throw new IllegalArgumentException("a run of symbols runs from low to high inside"
                        + " the universe: " + from + ".." + to);
            }
            if (from <= SURROGATES_TO && to >= SURROGATES_FROM) {
                throw new IllegalArgumentException("a surrogate is half of a pair and not a"
                        + " character, so no run of symbols holds one: " + from + ".." + to);
            }
        }
    }

    public CodePoints {
        ranges = normalised(ranges);
    }

    /** Nothing at all. */
    public static final CodePoints NONE = new CodePoints(List.of());

    /** Every symbol there is: the scalar values, the surrogates not among them. */
    public static final CodePoints EVERYTHING = new CodePoints(List.of(
            new Range(0, SURROGATES_FROM - 1), new Range(SURROGATES_TO + 1, LAST)));

    /** Whether {@code codePoint} is a surrogate, which is no symbol. */
    public static boolean isSurrogate(int codePoint) {
        return codePoint >= SURROGATES_FROM && codePoint <= SURROGATES_TO;
    }

    /** Just this one, which is a scalar value: a surrogate handed here is a symbol nothing reads. */
    public static CodePoints of(int symbol) {
        return new CodePoints(List.of(new Range(symbol, symbol)));
    }

    /**
     * What the five line terminators are, which is what a pattern's {@code .} leaves out
     * (spec §string-patterns).
     *
     * <p>Longer than the two a reader expects: a line feed, a carriage return, the next-line
     * character, and the two separators. {@code .} is the universe less these — and a negated class
     * is not, which is why neither is written as a rule and both are written as a difference.
     */
    public static final CodePoints LINE_TERMINATORS = of('\n').or(of('\r'))
            .or(of(0x85)).or(of(0x2028)).or(of(0x2029));

    /** What a pattern's {@code \d} holds: the ten ASCII digits and no other. */
    public static final CodePoints DIGITS = between('0', '9');

    /** What a pattern's {@code \w} holds: the ASCII letters, the ASCII digits and the underscore. */
    public static final CodePoints WORD = between('a', 'z').or(between('A', 'Z'))
            .or(DIGITS).or(of('_'));

    /**
     * What a pattern's {@code \s} holds: a space, a tab, a line feed, a vertical tab, a form feed
     * and a carriage return.
     *
     * <p>Not String whitespace (spec §string-whitespace), which is what {@code trim} and
     * {@code words} read. The two are separate sets the specification states separately, and a
     * pattern's shorthand is this one.
     */
    public static final CodePoints SPACES = of(' ').or(between('\t', '\r'));

    /**
     * Every symbol from one to another, both ends in it: the scalar values between them, so a run
     * across the surrogates leaves them out.
     *
     * <p>Both ends are symbols. A range whose end is a surrogate names a character that is not
     * one, and whoever read the pattern refuses it before this is asked.
     */
    public static CodePoints between(int from, int to) {
        if (isSurrogate(from) || isSurrogate(to)) {
            throw new IllegalArgumentException("a surrogate is half of a pair and not a character,"
                    + " so it ends no run of symbols: " + from + ".." + to);
        }
        return new CodePoints(scalarsIn(from, to));
    }

    /** Every symbol below {@code symbol}, which is the order symbols are compared in. */
    public static CodePoints below(int symbol) {
        if (symbol < 0 || symbol > LAST) {
            throw new IllegalArgumentException("no symbol is " + symbol);
        }
        return symbol > 0 ? new CodePoints(scalarsIn(0, symbol - 1)) : NONE;
    }

    /**
     * The runs the scalar values in {@code from..to} make, one or two of them or none.
     *
     * <p>None only where the interval lies within the surrogates. An interval running backwards is
     * no interval at all, and is refused here rather than read as holding nothing: every way a run
     * is made comes through this, so a caller that got its ends the wrong way round is told so
     * whichever way it came.
     */
    private static List<Range> scalarsIn(int from, int to) {
        if (from > to) {
            throw new IllegalArgumentException("a run of symbols runs from low to high: "
                    + from + ".." + to);
        }
        List<Range> out = new ArrayList<>();
        if (from < SURROGATES_FROM) {
            out.add(new Range(from, Math.min(to, SURROGATES_FROM - 1)));
        }
        if (to > SURROGATES_TO) {
            out.add(new Range(Math.max(from, SURROGATES_TO + 1), to));
        }
        return out;
    }

    /** Whether {@code symbol} is one of these. */
    public boolean has(int symbol) {
        for (Range each : ranges) {
            if (symbol >= each.from() && symbol <= each.to()) {
                return true;
            }
            if (symbol < each.from()) {
                return false;
            }
        }
        return false;
    }

    public boolean isEmpty() {
        return ranges.isEmpty();
    }

    /** Whether these are every symbol there is. */
    public boolean isEverything() {
        return ranges.equals(EVERYTHING.ranges);
    }

    /** Either of them. */
    public CodePoints or(CodePoints other) {
        List<Range> both = new ArrayList<>(ranges);
        both.addAll(other.ranges);
        return new CodePoints(both);
    }

    /** Both of them. */
    public CodePoints and(CodePoints other) {
        return not().or(other.not()).not();
    }

    /** These, less those. */
    public CodePoints less(CodePoints other) {
        return and(other.not());
    }

    /** Every symbol these are not, which is a set of scalar values like any other. */
    public CodePoints not() {
        List<Range> out = new ArrayList<>();
        int next = 0;
        for (Range each : ranges) {
            if (each.from() > next) {
                out.addAll(scalarsIn(next, each.from() - 1));
            }
            next = each.to() + 1;
        }
        if (next <= LAST) {
            out.addAll(scalarsIn(next, LAST));
        }
        return new CodePoints(out);
    }

    /**
     * The least symbol in these, which is what a reading walks to first.
     *
     * <p>Asked only of a set that has one. What it is for is choosing the same value on two runs
     * over one model, and a set with nothing in it is one nothing is chosen from.
     */
    public int least() {
        if (ranges.isEmpty()) {
            throw new IllegalStateException("nothing is the least of no symbols");
        }
        return ranges.get(0).from();
    }

    /** How many symbols these hold, which a caller bounding its work asks. */
    public long size() {
        long out = 0;
        for (Range each : ranges) {
            out += (long) each.to() - each.from() + 1;
        }
        return out;
    }

    /** The same runs, sorted and joined so that one set has one spelling. */
    private static List<Range> normalised(List<Range> given) {
        List<Range> sorted = new ArrayList<>(given);
        sorted.sort((a, b) -> a.from() != b.from()
                ? Integer.compare(a.from(), b.from()) : Integer.compare(a.to(), b.to()));
        List<Range> out = new ArrayList<>();
        for (Range each : sorted) {
            if (out.isEmpty()) {
                out.add(each);
                continue;
            }
            Range last = out.get(out.size() - 1);
            // Touching as well as overlapping. `a..b` beside `b+1..c` is one run, and left as two
            // the same set would have two spellings and two of them would not be equal.
            if (each.from() <= last.to() + 1) {
                out.set(out.size() - 1, new Range(last.from(), Math.max(last.to(), each.to())));
            } else {
                out.add(each);
            }
        }
        return List.copyOf(out);
    }

    @Override
    public String toString() {
        StringBuilder out = new StringBuilder("{");
        for (Range each : ranges) {
            if (out.length() > 1) {
                out.append(' ');
            }
            out.append(String.format("%04X", each.from()));
            if (each.to() != each.from()) {
                out.append('-').append(String.format("%04X", each.to()));
            }
        }
        return out.append('}').toString();
    }
}
