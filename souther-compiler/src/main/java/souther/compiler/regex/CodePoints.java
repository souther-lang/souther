package souther.compiler.regex;

import java.util.ArrayList;
import java.util.List;

/**
 * A set of the symbols a Java pattern reads a string as.
 *
 * <p><b>Not Unicode scalar values.</b> What a matcher advances over is a code point where the string
 * holds a well-formed surrogate pair, and the code unit itself where it holds half of one — a lone
 * high surrogate is one symbol to a pattern, and {@code .} accepts it. So the universe is
 * {@code 0..0x10FFFF} with the surrogate range in it, and a reading that took those out would refuse
 * strings the engine accepts.
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

    /** One run of symbols, both ends in it. */
    public record Range(int from, int to) {

        public Range {
            if (from < 0 || to > LAST || from > to) {
                throw new IllegalArgumentException("a run of symbols runs from low to high inside"
                        + " the universe: " + from + ".." + to);
            }
        }
    }

    public CodePoints {
        ranges = normalised(ranges);
    }

    /** Nothing at all. */
    public static final CodePoints NONE = new CodePoints(List.of());

    /** Every symbol a pattern can read, the surrogate range among them. */
    public static final CodePoints EVERYTHING = new CodePoints(List.of(new Range(0, LAST)));

    /**
     * What the five line terminators are.
     *
     * <p>Java's own list, and it is longer than the two a reader expects: a line feed, a carriage
     * return, the next-line character, and the two separators. {@code .} is the universe less these
     * — and a negated class is not, which is why neither is written as a rule and both are written
     * as a difference.
     */
    public static final CodePoints LINE_TERMINATORS = of('\n').or(of('\r'))
            .or(of(0x85)).or(of(0x2028)).or(of(0x2029));

    /** Just this one. */
    public static CodePoints of(int symbol) {
        return new CodePoints(List.of(new Range(symbol, symbol)));
    }

    /** Every symbol from one to another, both ends in it. */
    public static CodePoints between(int from, int to) {
        return new CodePoints(List.of(new Range(from, to)));
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
        return ranges.size() == 1 && ranges.get(0).from() == 0 && ranges.get(0).to() == LAST;
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

    /** Everything these are not. */
    public CodePoints not() {
        List<Range> out = new ArrayList<>();
        int next = 0;
        for (Range each : ranges) {
            if (each.from() > next) {
                out.add(new Range(next, each.from() - 1));
            }
            next = each.to() + 1;
        }
        if (next <= LAST) {
            out.add(new Range(next, LAST));
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
