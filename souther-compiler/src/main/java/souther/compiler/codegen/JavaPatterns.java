package souther.compiler.codegen;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import souther.compiler.regex.CodePoints;
import souther.compiler.regex.PatternMeaning;

/**
 * A pattern's meaning written in {@code java.util.regex}'s language, for the JVM to run.
 *
 * <p>The JVM's matcher is a target here, as bytecode is: what it is handed is written from the
 * {@link PatternMeaning} the checker read, never the text the author wrote. So what a pattern
 * accepts on the JVM is what the meaning says, whichever constructs the author's text used and
 * whatever the JVM's engine would have made of them.
 *
 * <p>Written only in constructs whose meaning does not depend on a flag or on the engine's reading
 * of a class. A set of symbols is written as its ranges by number — never as {@code .}, {@code \d},
 * {@code \s} or {@code \w}, whose sets are the engine's to decide — and a group never captures.
 * Nothing is written that the meaning does not hold, so there is no anchor, no lookaround and no
 * possessive or reluctant count: whole-string matching, which {@code Matcher.matches} is, is what
 * the meaning is stated against.
 */
public final class JavaPatterns {

    /** A class of no symbol: the complement of every code point, which the engine accepts as a
     *  class and no character is in. */
    private static final String NO_SYMBOL = "[^\\x{0}-\\x{10FFFF}]";

    private JavaPatterns() {
    }

    /** {@code meaning} as a pattern whose whole-string match accepts exactly the strings it does. */
    public static String of(PatternMeaning meaning) {
        StringBuilder out = new StringBuilder();
        choice(meaning, out);
        return out.toString();
    }

    /** Written where a choice may stand bare: the whole pattern, or the inside of a group. */
    private static void choice(PatternMeaning meaning, StringBuilder out) {
        if (meaning instanceof PatternMeaning.EitherOf it) {
            for (int i = 0; i < it.arms().size(); i++) {
                if (i > 0) {
                    out.append('|');
                }
                sequence(it.arms().get(i), out);
            }
            return;
        }
        sequence(meaning, out);
    }

    /** Written where a sequence may stand bare: one arm of a choice, or a part of a sequence. */
    private static void sequence(PatternMeaning meaning, StringBuilder out) {
        switch (meaning) {
            case PatternMeaning.Nothing _ -> { }
            case PatternMeaning.InTurn it -> it.parts().forEach(each -> sequence(each, out));
            case PatternMeaning.EitherOf _ -> group(meaning, out);
            case PatternMeaning.Never _, PatternMeaning.Symbols _, PatternMeaning.Repeated _ ->
                    atom(meaning, out);
        }
    }

    /** Written where one unit has to stand: what a count applies to. */
    private static void atom(PatternMeaning meaning, StringBuilder out) {
        switch (meaning) {
            case PatternMeaning.Symbols it -> symbols(it.held(), out);
            case PatternMeaning.Never _ -> out.append(NO_SYMBOL);
            case PatternMeaning.Repeated it -> repeated(it, out);
            case PatternMeaning.Nothing _, PatternMeaning.InTurn _, PatternMeaning.EitherOf _ ->
                    group(meaning, out);
        }
    }

    private static void repeated(PatternMeaning.Repeated it, StringBuilder out) {
        // What is repeated is always grouped when it is itself a repetition. Written bare, the
        // count after a count is the engine's possessive or reluctant marker rather than a second
        // count.
        if (it.what() instanceof PatternMeaning.Repeated) {
            group(it.what(), out);
        } else {
            atom(it.what(), out);
        }
        out.append('{').append(it.least());
        if (it.unbounded()) {
            out.append(',');
        } else if (it.most() != it.least()) {
            out.append(',').append(it.most());
        }
        out.append('}');
    }

    private static void group(PatternMeaning meaning, StringBuilder out) {
        out.append("(?:");
        choice(meaning, out);
        out.append(')');
    }

    /**
     * A set of symbols, as a class of its ranges.
     *
     * <p>One symbol on its own is written without a class. An ASCII letter or digit is written as
     * itself, which is what it is in every reading of the engine's; the rest of printable ASCII is
     * written after a backslash, which the engine reads as the character itself before anything that
     * is not a letter, inside a class or out of one. Every other symbol is written by its number:
     * which characters are special where, and which a flag would change, are the engine's to know,
     * and a number is the one spelling none of them affects. What is written is also what a decoder's
     * {@code invalid_format} carries, so a format a person wrote reads close to how they wrote it.
     */
    private static void symbols(CodePoints held, StringBuilder out) {
        // A class that lists nothing is no pattern to the engine, so the empty set is written as
        // what accepts no string.
        if (held.isEmpty()) {
            out.append(NO_SYMBOL);
            return;
        }
        if (held.size() == 1) {
            symbol(held.least(), out);
            return;
        }
        // The shorter of the set and what it leaves out. The engine tries a class a range at a
        // time, so `.` written as its eight ranges is eight tries a symbol, and written as the five
        // symbols it leaves out it is one class of five. What it leaves out is taken over every
        // code point, the surrogates among them: no string holds one, so no string can tell the two
        // apart.
        List<int[]> left = leftOut(held);
        if (left.isEmpty()) {
            // Every symbol. A class leaving out nothing is no class to the engine.
            out.append("[\\x{0}-\\x{10FFFF}]");
            return;
        }
        if (left.size() < held.ranges().size()) {
            out.append("[^");
            left.forEach(each -> range(each[0], each[1], out));
        } else {
            out.append('[');
            held.ranges().forEach(each -> range(each.from(), each.to(), out));
        }
        out.append(']');
    }

    /** The runs of code points {@code held} leaves out, the surrogates included. */
    private static List<int[]> leftOut(CodePoints held) {
        List<int[]> out = new ArrayList<>();
        int next = 0;
        for (CodePoints.Range each : held.ranges()) {
            // A gap that is only the surrogates is no gap to a string, and leaving it out keeps a
            // set that runs across them one range.
            if (each.from() > next && !(next == SURROGATES_FROM && each.from() == SURROGATES_TO + 1)) {
                out.add(new int[] {next, each.from() - 1});
            }
            next = each.to() + 1;
        }
        if (next <= CodePoints.LAST) {
            out.add(new int[] {next, CodePoints.LAST});
        }
        return out;
    }

    private static final int SURROGATES_FROM = 0xD800;
    private static final int SURROGATES_TO = 0xDFFF;

    private static void range(int from, int to, StringBuilder out) {
        symbol(from, out);
        if (to != from) {
            out.append('-');
            symbol(to, out);
        }
    }

    private static void symbol(int point, StringBuilder out) {
        if (plain(point)) {
            out.appendCodePoint(point);
        } else if (point > ' ' && point < 0x7F) {
            out.append('\\').appendCodePoint(point);
        } else {
            out.append("\\x{").append(Integer.toHexString(point).toUpperCase(Locale.ROOT))
                    .append('}');
        }
    }

    private static boolean plain(int point) {
        return (point >= 'a' && point <= 'z') || (point >= 'A' && point <= 'Z')
                || (point >= '0' && point <= '9');
    }
}
