package souther.compiler.partition;

import java.util.ArrayList;
import java.util.List;
import java.util.Optional;

/**
 * A string the pattern an invariant states would accept.
 *
 * <p>A format rule is the commonest thing an identifier says about itself — an office number is
 * {@code [0-9]{2}-[0-9]{6}}, an invoice is {@code INV-[0-9]{4}-[0-9]{6}} — and until now nothing could
 * write one. A record holding one could not be composed at all, so every combination it took part in
 * came back as one whose values were refused, and a generator that could name the gaps could fill none
 * of them. Twenty-seven of the patterns in the example models are of this kind.
 *
 * <p>What comes out is the shortest string the pattern accepts, chosen the same way every time: the
 * first branch of an alternation, the first character of a class, the fewest repetitions a bound
 * allows. Nothing here is random. A generated row is compared against the last one to see what changed,
 * and a value that differed between two runs of the same model would make every row look changed.
 *
 * <p>What it does not understand, it does not guess at. The result is put back through the pattern
 * before it is offered, so a construct this reads wrongly produces nothing rather than a value that
 * does not match — the caller already knows what to do with nothing, which is to say so.
 */
final class PatternValues {

    /** How many repetitions an unbounded quantifier is asked for beyond its minimum. None: the
     * shortest string the pattern accepts is the one that says least about anything else. */
    private static final int BEYOND_MINIMUM = 0;

    /** Where a negated class takes its character from, in order. A letter first, because an
     * identifier that excludes something usually excludes punctuation. */
    private static final String PREFERRED = "abcdefghijklmnopqrstuvwxyz"
            + "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";

    /**
     * The shortest string {@code regex} accepts, or empty where this cannot say.
     *
     * <p>Empty for a construct it does not read — a backreference, a lookaround, a unicode property —
     * and empty for anything it built that the pattern then refused, which is the same answer and the
     * reason the second check is here.
     */
    static Optional<String> shortestAccepted(String regex) {
        PatternValues reader = new PatternValues(regex);
        String built;
        try {
            built = reader.alternation();
            if (!reader.done()) {
                return Optional.empty();   // stopped early — an unbalanced bracket, say
            }
        } catch (Unreadable | StackOverflowError _) {
            return Optional.empty();
        }
        try {
            return java.util.regex.Pattern.matches(regex, built)
                    ? Optional.of(built) : Optional.empty();
        } catch (java.util.regex.PatternSyntaxException _) {
            // Not a pattern at all. The compiler settles that where it is written, so nothing here
            // reports it again; what it means for a value is that there is none.
            return Optional.empty();
        }
    }

    /** A construct this does not read. Thrown rather than returned so that a nested one stops the
     * whole walk: half of a pattern is not a value. */
    private static final class Unreadable extends RuntimeException {
        Unreadable() {
            super(null, null, false, false);
        }
    }

    private final String regex;
    private int at;

    private PatternValues(String regex) {
        this.regex = regex;
        this.at = 0;
    }

    // --- the grammar ------------------------------------------------------------------------------

    /** {@code a|b|c} — the first branch, always. The rest is still read, because a pattern this
     * cannot read all of is one it will not offer a value for. */
    private String alternation() {
        String first = sequence();
        while (peek() == '|') {
            take();
            sequence();
        }
        return first;
    }

    private String sequence() {
        StringBuilder out = new StringBuilder();
        while (!done() && peek() != '|' && peek() != ')') {
            out.append(quantified());
        }
        return out.toString();
    }

    private String quantified() {
        String one = atom();
        int least = 1;
        int most = 1;
        switch (peek()) {
            case '?' -> { take(); least = 0; most = 1; }
            case '*' -> { take(); least = 0; most = Integer.MAX_VALUE; }
            case '+' -> { take(); least = 1; most = Integer.MAX_VALUE; }
            case '{' -> {
                take();
                least = number();
                most = least;
                if (peek() == ',') {
                    take();
                    most = peek() == '}' ? Integer.MAX_VALUE : number();
                }
                expect('}');
            }
            default -> { }
        }
        // A reluctant or possessive marker changes what a matcher does, not what the language accepts.
        if (peek() == '?' || peek() == '+') {
            take();
        }
        int times = least + (most == least ? 0 : Math.min(BEYOND_MINIMUM, most - least));
        return one.repeat(times);
    }

    private String atom() {
        char c = peek();
        switch (c) {
            case '(' -> {
                take();
                if (peek() == '?') {
                    take();
                    // Only a plain non-capturing group. A lookaround or a named group says something
                    // about the match that a value cannot be built from by reading left to right.
                    if (peek() != ':') {
                        throw new Unreadable();
                    }
                    take();
                }
                String inside = alternation();
                expect(')');
                return inside;
            }
            case '[' -> {
                take();
                return characterClass();
            }
            case '\\' -> {
                take();
                return escaped();
            }
            case '.' -> {
                take();
                return "a";
            }
            case '^', '$' -> {
                // The whole string is matched anyway, so an anchor at either end says nothing extra.
                take();
                return "";
            }
            case 0 -> throw new Unreadable();
            default -> {
                take();
                return String.valueOf(c);
            }
        }
    }

    // --- character classes -------------------------------------------------------------------------

    /** {@code [a-z0-9_]} or {@code [^@\s]} — one character it accepts. */
    private String characterClass() {
        boolean negated = peek() == '^';
        if (negated) {
            take();
        }
        List<char[]> ranges = new ArrayList<>();
        boolean first = true;
        while (!done() && (peek() != ']' || first)) {
            first = false;
            char low = classMember();
            if (peek() == '-' && at + 1 < regex.length() && regex.charAt(at + 1) != ']') {
                take();
                ranges.add(new char[] {low, classMember()});
            } else {
                ranges.add(new char[] {low, low});
            }
        }
        expect(']');
        if (ranges.isEmpty()) {
            throw new Unreadable();
        }
        if (!negated) {
            return String.valueOf(ranges.get(0)[0]);
        }
        for (char candidate : PREFERRED.toCharArray()) {
            if (ranges.stream().noneMatch(r -> candidate >= r[0] && candidate <= r[1])) {
                return String.valueOf(candidate);
            }
        }
        throw new Unreadable();
    }

    /** One character of a class, which may be written as an escape. A shorthand inside a class covers
     * several characters at once; the first of what it stands for is enough to be in the class, and to
     * be out of a negated one it has to be excluded as a whole — which is why the shorthand's whole
     * range is added. */
    private char classMember() {
        char c = take();
        if (c != '\\') {
            return c;
        }
        char kind = take();
        return switch (kind) {
            case 'd' -> '0';
            case 'w' -> 'a';
            case 's' -> ' ';
            case 'n' -> '\n';
            case 't' -> '\t';
            case 'r' -> '\r';
            case 'D', 'W', 'S', 'p', 'P', 'b', 'B' -> throw new Unreadable();
            default -> kind;   // an escaped literal: `\-`, `\.`, `\\`, `\+`
        };
    }

    /** An escape outside a class. */
    private String escaped() {
        char kind = take();
        return switch (kind) {
            case 'd' -> "0";
            case 'w' -> "a";
            case 's' -> " ";
            case 'n' -> "\n";
            case 't' -> "\t";
            case 'r' -> "\r";
            case 'D', 'W', 'S', 'p', 'P', 'b', 'B', 'k', 'Q', 'E', 'G', 'A', 'Z', 'z' ->
                    throw new Unreadable();
            case '0', '1', '2', '3', '4', '5', '6', '7', '8', '9' -> throw new Unreadable();   // a back reference
            default -> String.valueOf(kind);
        };
    }

    // --- reading ------------------------------------------------------------------------------------

    private int number() {
        int start = at;
        while (!done() && Character.isDigit(peek())) {
            take();
        }
        if (start == at) {
            throw new Unreadable();
        }
        return Integer.parseInt(regex.substring(start, at));
    }

    private boolean done() {
        return at >= regex.length();
    }

    private char peek() {
        return done() ? 0 : regex.charAt(at);
    }

    private char take() {
        if (done()) {
            throw new Unreadable();
        }
        return regex.charAt(at++);
    }

    private void expect(char c) {
        if (take() != c) {
            throw new Unreadable();
        }
    }
}
