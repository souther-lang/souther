package souther.compiler.partition;

import java.nio.charset.StandardCharsets;
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

    /**
     * How long a value this will write. Past this the pattern is asking for something no row wants:
     * an observation reads a string back to a bounded length, so a longer one could not be compared
     * against what it produced anyway.
     */
    private static final int LONGEST = 1024;

    /**
     * How much backing up the answer is allowed to ask the engine for.
     *
     * <p>The answer is checked by putting it back through the pattern, and that check is the only
     * unbounded thing here: the engine tries and backs up, and a repetition written over something of
     * more than one length gives it somewhere to back up to for every copy in the string. Those
     * multiply, so a pattern this reads perfectly well can take longer to check than anybody will wait
     * — {@code (?:x?x){40}} is one, and the value it asks to have checked is forty characters long.
     *
     * <p>Twenty, because at twenty the check is under a millisecond and at thirty-three it is a fifth
     * of a second and still doubling. What a real rule asks for is nothing like either: the most any
     * of the format rules in the example models asks for is five.
     */
    private static final int MOST_BACKTRACKING = 20;

    /**
     * Where a negated class takes its character from, in order.
     *
     * <p>A letter first, because a class that excludes something usually excludes punctuation, and a
     * value made of letters is the one a reader recognises. Then the rest of printable ASCII, and then
     * a character from each of the alphabets a model here is written in — a rule excluding ASCII
     * entirely is asking for one of those. The three a literal spells but nobody sees last: they read
     * as nothing at all in a row, so they are what is left when a rule excludes every character that
     * reads as something.
     */
    private static final String PREFERRED = build();

    private static String build() {
        StringBuilder out = new StringBuilder("abcdefghijklmnopqrstuvwxyz"
                + "ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789");
        for (char c = 0x20; c <= 0x7e; c++) {
            out.append(c);
        }
        out.append("あアー一　ｦ");
        return out.append('\t').append('\n').append('\r').toString();
    }

    /**
     * Whether a row can be written carrying this.
     *
     * <p>Two things have to hold, and they are about different places. The literal reads five escapes,
     * so a control character outside them would go into the row as itself — not a value anybody can
     * read. And the row is a line of a source file, so the value has to survive being encoded into
     * one: a lone surrogate is half of a character, which UTF-8 has nothing to write and replaces with
     * a `?`, and the value somebody pastes is then not the value that was generated.
     *
     * <p>Either way there is no value here, which is what the caller already handles.
     */
    private static boolean writable(String value) {
        if (value.length() > LONGEST) {
            return false;
        }
        for (int i = 0; i < value.length(); i++) {
            char c = value.charAt(i);
            if (c != '\n' && c != '\t' && c != '\r' && (c < 0x20 || c == 0x7f)) {
                return false;
            }
        }
        return StandardCharsets.UTF_8.newEncoder().canEncode(value);
    }

    /**
     * The shortest string {@code regex} accepts, or empty where this cannot say.
     *
     * <p>Empty for a construct it does not read — a backreference, a lookaround, a unicode property —
     * and empty for anything it built that the pattern then refused, which is the same answer and the
     * reason the second check is here. Empty too for a string the pattern accepts and a row cannot
     * carry: what is wanted is a value somebody can paste into a model, not one that matches.
     */
    static Optional<String> shortestAccepted(String regex) {
        PatternValues reader = new PatternValues(regex);
        String built;
        try {
            built = reader.alternation().text();
            if (!reader.done()) {
                return Optional.empty();   // stopped early — an unbalanced bracket, say
            }
        } catch (Unreadable | StackOverflowError _) {
            return Optional.empty();
        }
        if (!writable(built)) {
            return Optional.empty();
        }
        try {
            return java.util.regex.Pattern.matches(regex, built)
                    ? Optional.of(built) : Optional.empty();
        } catch (java.util.regex.PatternSyntaxException | StackOverflowError _) {
            // Not a pattern at all, or one the engine cannot walk to the end of. The compiler settles
            // the first where it is written, so nothing here reports it again; what either means for a
            // value is that there is none.
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

    /**
     * What one part of a pattern writes, and what putting it back through the engine will cost.
     *
     * <p>The second is the point. The engine matches by trying and backing up, and where a repetition
     * is written over something that can itself match more than one length, every copy of it in the
     * generated string is another place to back up to — which multiplies. {@code (?:x?x){40}} is
     * forty of them over a forty-character string, and no part of it is a construct this cannot read.
     *
     * @param ambiguity how many places in {@code text} the engine may have to back up to, counted so
     *                  that a repetition multiplies what is under it rather than adding to it
     */
    private record Piece(String text, int ambiguity) {

        static final Piece NOTHING = new Piece("", 0);

        static Piece plain(String text) {
            return new Piece(text, 0);
        }

        Piece then(Piece next) {
            return new Piece(text + next.text(), ambiguity + next.ambiguity());
        }
    }

    /** {@code a|b|c} — the first branch, always. The rest is still read, because a pattern this
     * cannot read all of is one it will not offer a value for. A branch not taken is still somewhere
     * the engine can back up to, so having more than one costs. */
    private Piece alternation() {
        Piece first = sequence();
        int branches = 0;
        while (peek() == '|') {
            take();
            sequence();
            branches++;
        }
        return branches == 0 ? first : new Piece(first.text(), first.ambiguity() + branches);
    }

    private Piece sequence() {
        Piece out = Piece.NOTHING;
        while (!done() && peek() != '|' && peek() != ')') {
            out = out.then(quantified());
        }
        return out;
    }

    private Piece quantified() {
        Piece one = atom();
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
        if ((long) one.text().length() * times > LONGEST) {
            throw new Unreadable();   // longer than a row will carry, so there is no row to write
        }
        // A repetition that can stop early is a place to back up to whatever it wrote — even where it
        // wrote nothing, since the engine still has the choice. Each copy carries what is under it,
        // which is how a repetition of a repetition becomes the product of the two.
        boolean variable = most != least;
        int copies = Math.max(times, 1);
        long cost = (long) copies * one.ambiguity() + (variable ? copies : 0);
        if (cost > MOST_BACKTRACKING) {
            // Not a construct this cannot read — every part of it was read. What it cannot do is
            // check the answer in the time anybody has, and an answer it did not check is not one it
            // offers.
            throw new Unreadable();
        }
        return new Piece(one.text().repeat(times), (int) cost);
    }

    private Piece atom() {
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
                Piece inside = alternation();
                expect(')');
                return inside;
            }
            case '[' -> {
                take();
                return Piece.plain(characterClass());
            }
            case '\\' -> {
                take();
                return Piece.plain(escaped());
            }
            case '.' -> {
                take();
                return Piece.plain("a");
            }
            case '^', '$' -> {
                // The whole string is matched anyway, so an anchor at either end says nothing extra.
                take();
                return Piece.NOTHING;
            }
            case 0 -> throw new Unreadable();
            default -> {
                take();
                return Piece.plain(String.valueOf(c));
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
            List<char[]> member = classMember();
            if (member.size() == 1 && peek() == '-'
                    && at + 1 < regex.length() && regex.charAt(at + 1) != ']') {
                take();
                // The far end of a range is one character. A shorthand cannot be one: `[\d-z]` is
                // not a range this can read the ends of.
                List<char[]> upper = classMember();
                if (upper.size() != 1 || upper.get(0)[0] != upper.get(0)[1]) {
                    throw new Unreadable();
                }
                ranges.add(new char[] {member.get(0)[0], upper.get(0)[0]});
            } else {
                ranges.addAll(member);
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

    /**
     * What one member of a class stands for — the characters it puts in, as ranges.
     *
     * <p>Ranges rather than a character, because the two questions a class is asked want different
     * things from the same member. To pick a character the class accepts, one of them is enough. To
     * pick one a negated class accepts, all of them are needed: a member standing for the letters and
     * the digits excludes the letters and the digits, and a reader that recorded only the first of
     * them would go on to pick the second and produce a value the pattern refuses.
     */
    private List<char[]> classMember() {
        char c = take();
        if (c != '\\') {
            return one(c);
        }
        char kind = take();
        return switch (kind) {
            case 'd' -> List.of(new char[] {'0', '9'});
            case 'w' -> List.of(new char[] {'a', 'z'}, new char[] {'A', 'Z'},
                    new char[] {'0', '9'}, new char[] {'_', '_'});
            case 's' -> List.of(new char[] {' ', ' '}, new char[] {'\t', '\r'});
            case 'n' -> one('\n');
            case 't' -> one('\t');
            case 'r' -> one('\r');
            case 'x' -> one(hex(2));
            case 'u' -> one(hex(4));
            case 'D', 'W', 'S', 'p', 'P', 'b', 'B', 'c' -> throw new Unreadable();
            default -> one(kind);   // an escaped literal: `\-`, `\.`, `\\`, `\+`
        };
    }

    private static List<char[]> one(char c) {
        return List.of(new char[] {c, c});
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
            case 'x' -> String.valueOf(hex(2));
            case 'u' -> String.valueOf(hex(4));
            case 'D', 'W', 'S', 'p', 'P', 'b', 'B', 'c', 'k', 'Q', 'E', 'G', 'A', 'Z', 'z' ->
                    throw new Unreadable();
            case '0', '1', '2', '3', '4', '5', '6', '7', '8', '9' -> throw new Unreadable();   // a back reference
            default -> String.valueOf(kind);
        };
    }

    /** A hex escape — two digits after {@code x}, four after {@code u} — as the character it names.
     * Read rather than refused because a class written that way is usually one excluding ASCII, and
     * what it is asking for is a character from one of the alphabets a model is written in. */
    private char hex(int digits) {
        int value = 0;
        for (int i = 0; i < digits; i++) {
            int digit = Character.digit(take(), 16);
            if (digit < 0) {
                throw new Unreadable();
            }
            value = value * 16 + digit;
        }
        return (char) value;
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
        try {
            return Integer.parseInt(regex.substring(start, at));
        } catch (NumberFormatException _) {
            // A count past what an int holds. Whether the pattern engine reads it at all is its own
            // business; what it is here is a bound this cannot answer with a value.
            throw new Unreadable();
        }
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
