package souther.compiler.regex;

import java.util.ArrayList;
import java.util.List;

/**
 * The subset of Java's pattern language this compiler reads, as what it accepts.
 *
 * <p>The one place the subset is decided. What this reads is what is supported and what it refuses
 * is what is not — a second reader answering the same question is a second boundary, and the day one
 * of them widens, a pattern is supported by whichever was asked.
 *
 * <p><b>Exactly what Java accepts, for what it reads at all.</b> Where a construct is in the subset,
 * the strings this says the pattern accepts are the strings {@code java.util.regex} accepts: `.`
 * leaves out the five line terminators and nothing else, a negated class leaves out only what is
 * written in it, and the shorthands hold what they hold without a flag to widen them. A subset that
 * narrowed a construct it claimed would be worse than refusing it, since a narrower set still holds
 * the values somebody wrote and nothing would say the answer had shrunk.
 *
 * <p>Nothing here chooses a value. What one string of the language would be is a question for
 * whatever holds the language; a reader that answered it while parsing is the arrangement that lost
 * the second arm of every choice and the ceiling of every repetition.
 */
public final class PatternParser {

    /**
     * How deep a pattern may be written.
     *
     * <p>The reading is recursive, so what bounds it is the stack. Past this the answer is that the
     * pattern is not read rather than a stack overflow somewhere inside a compile — the two are the
     * same fact about this reader and only one of them is something a caller can act on.
     */
    private static final int DEEPEST = 200;

    private final String regex;
    private int at;
    private int depth;

    private PatternParser(String regex) {
        this.regex = regex;
        this.at = 0;
        this.depth = 0;
    }

    /** What {@code regex} accepts, or which construct in it this does not read. */
    public static PatternRead read(String regex) {
        if (regex == null) {
            throw new IllegalArgumentException("a pattern is some string");
        }
        PatternParser reader = new PatternParser(regex);
        try {
            PatternSyntax syntax = reader.alternation();
            if (!reader.done()) {
                // A bracket closing nothing, which is what is left when the reading of a choice
                // stops before the end.
                return new PatternRead.NotRead(PatternRead.Unsupported.SOMETHING_UNCLOSED);
            }
            // Every anchor has to come to something, and what it comes to is settled by where it
            // stands rather than by how it is written. Asked here so that a pattern this cannot
            // settle is one it says it did not read: the tree is kept as the author wrote it, and
            // what the anchors come to is worked out again by whoever builds the machine.
            if (PatternSyntax.withoutAnchors(syntax) == null) {
                return new PatternRead.NotRead(PatternRead.Unsupported.AN_ANCHOR_THIS_CANNOT_PLACE);
            }
            return new PatternRead.Read(syntax);
        } catch (Refused refused) {
            return new PatternRead.NotRead(refused.why);
        }
    }

    // --- the grammar ------------------------------------------------------------------------------

    private PatternSyntax alternation() {
        List<PatternSyntax> arms = new ArrayList<>();
        arms.add(sequence());
        while (peek() == '|') {
            take();
            arms.add(sequence());
        }
        return arms.size() == 1 ? arms.get(0) : new PatternSyntax.EitherOf(arms);
    }

    private PatternSyntax sequence() {
        List<PatternSyntax> parts = new ArrayList<>();
        while (!done() && peek() != '|' && peek() != ')') {
            PatternSyntax one = quantified();
            // A group of nothing is nothing, and is left out so that one written pattern has one
            // tree. An anchor is not one of those: where it stands is what decides what it comes
            // to, so dropping it here would be answering that question with the one place that
            // cannot see the answer.
            if (!(one instanceof PatternSyntax.Nothing)) {
                parts.add(one);
            }
        }
        return switch (parts.size()) {
            case 0 -> new PatternSyntax.Nothing();
            case 1 -> parts.get(0);
            default -> new PatternSyntax.InTurn(parts);
        };
    }

    private PatternSyntax quantified() {
        PatternSyntax one = atom();
        int least;
        int most;
        switch (peek()) {
            case '?' -> { take(); least = 0; most = 1; }
            case '*' -> { take(); least = 0; most = PatternSyntax.Repeated.NO_CEILING; }
            case '+' -> { take(); least = 1; most = PatternSyntax.Repeated.NO_CEILING; }
            case '{' -> {
                take();
                least = count();
                most = least;
                if (peek() == ',') {
                    take();
                    most = peek() == '}' ? PatternSyntax.Repeated.NO_CEILING : count();
                }
                expect('}');
                if (most != PatternSyntax.Repeated.NO_CEILING && most < least) {
                    throw new Refused(PatternRead.Unsupported.A_COUNT_THIS_CANNOT_READ);
                }
            }
            default -> {
                return one;
            }
        }
        // Reluctant says how a matcher walks and not which strings are accepted: it takes as few
        // copies as it can and takes more where the rest of the pattern needs them, so what is
        // matched whole is matched either way. The marker is read and left out of what this holds.
        if (peek() == '?') {
            take();
        } else if (peek() == '+') {
            // Possessive is not one of those. It takes what it can and gives none of it back, so a
            // body that accepts the empty string takes it once and refuses to try again:
            // {@code (?:|a)++} matches nothing that {@code (?:|a)+} matches beyond the empty
            // string. Read as the plain one, this compiler answered for a wider language than the
            // author wrote.
            throw new Refused(PatternRead.Unsupported.A_POSSESSIVE_REPETITION);
        }
        return new PatternSyntax.Repeated(one, least, most);
    }

    private PatternSyntax atom() {
        char c = peek();
        return switch (c) {
            case '(' -> group();
            case '[' -> {
                take();
                yield new PatternSyntax.Symbols(characterClass());
            }
            case '\\' -> {
                take();
                yield new PatternSyntax.Symbols(escaped());
            }
            case '.' -> {
                take();
                // Every symbol but the five Java calls line terminators. Written as a difference
                // rather than as a rule of its own, so that a negated class beside it — which does
                // not leave them out — is the same algebra with a different set taken away.
                yield new PatternSyntax.Symbols(CodePoints.EVERYTHING
                        .less(CodePoints.LINE_TERMINATORS));
            }
            case '^', '$' -> {
                boolean end = peek() == '$';
                take();
                yield new PatternSyntax.Anchor(end);
            }
            // A brace that begins no count. Java refuses it, so a pattern holding one names no
            // language at all — read as an ordinary character it would be this compiler answering
            // for a pattern the author cannot run.
            case '{' -> throw new Refused(PatternRead.Unsupported.A_COUNT_THIS_CANNOT_READ);
            case '*', '+', '?' -> throw new Refused(PatternRead.Unsupported.SOMETHING_UNCLOSED);
            case 0 -> throw new Refused(PatternRead.Unsupported.SOMETHING_UNCLOSED);
            default -> new PatternSyntax.Symbols(CodePoints.of(literal()));
        };
    }

    /** A group, which this reads only where it says nothing about the match. */
    private PatternSyntax group() {
        expect('(');
        if (peek() == '?') {
            take();
            // `(?:` and nothing else. A lookaround, a named group and a flag group each say
            // something about where a match sits or how it is walked, which no set of strings holds.
            if (peek() != ':') {
                throw new Refused(PatternRead.Unsupported.A_GROUP_ABOUT_THE_MATCH);
            }
            take();
        }
        deeper();
        PatternSyntax inside = alternation();
        shallower();
        expect(')');
        return inside;
    }

    // --- character classes -------------------------------------------------------------------------

    /** What is between `[` and `]`, as the symbols it holds. The `[` is already taken. */
    private CodePoints characterClass() {
        boolean negated = peek() == '^';
        if (negated) {
            take();
        }
        CodePoints held = CodePoints.NONE;
        boolean first = true;
        while (!done() && (peek() != ']' || first)) {
            first = false;
            if (peek() == '[') {
                // A class inside a class, which Java reads as a union or an intersection depending
                // on the `&&` beside it. Neither is read here.
                throw new Refused(PatternRead.Unsupported.A_CLASS_OF_CLASSES);
            }
            if (peek() == '&' && at + 1 < regex.length() && regex.charAt(at + 1) == '&') {
                throw new Refused(PatternRead.Unsupported.A_CLASS_OF_CLASSES);
            }
            held = held.or(classMember());
        }
        expect(']');
        if (held.isEmpty()) {
            throw new Refused(PatternRead.Unsupported.SOMETHING_UNCLOSED);
        }
        // The universe less what is written, and not a set of what a reader thought was left. A
        // negated class does not leave out the line terminators, which is the whole reason `.` is
        // written as its own difference.
        return negated ? held.not() : held;
    }

    /**
     * One member of a class, which is a symbol, a run of them, or a shorthand's whole set.
     *
     * <p>A run is read only where both ends are one symbol. {@code [\d-z]} names no run: what is on
     * the left of the dash is ten symbols, and there is no such thing as the range from ten symbols
     * to one.
     */
    private CodePoints classMember() {
        CodePoints member = classAtom();
        boolean isOne = member.size() == 1;
        if (isOne && peek() == '-' && at + 1 < regex.length() && regex.charAt(at + 1) != ']') {
            take();
            CodePoints upper = classAtom();
            if (upper.size() != 1) {
                throw new Refused(PatternRead.Unsupported.AN_ESCAPE_THIS_DOES_NOT_READ);
            }
            if (upper.least() < member.least()) {
                throw new Refused(PatternRead.Unsupported.A_COUNT_THIS_CANNOT_READ);
            }
            return CodePoints.between(member.least(), upper.least());
        }
        return member;
    }

    private CodePoints classAtom() {
        if (peek() == '\\') {
            take();
            return escaped();
        }
        return CodePoints.of(literal());
    }

    // --- escapes -----------------------------------------------------------------------------------

    /** What an escape stands for, as symbols. The backslash is already taken. */
    private CodePoints escaped() {
        if (done()) {
            throw new Refused(PatternRead.Unsupported.AN_ESCAPE_THIS_DOES_NOT_READ);
        }
        char kind = peek();
        return switch (kind) {
            // The shorthands, as Java holds them without a flag to widen them: the digits are the
            // ten ASCII ones, a word character is ASCII with the underscore, and the whitespace is
            // the six Java names.
            case 'd' -> { take(); yield digits(); }
            case 'D' -> { take(); yield digits().not(); }
            case 'w' -> { take(); yield word(); }
            case 'W' -> { take(); yield word().not(); }
            case 's' -> { take(); yield whitespace(); }
            case 'S' -> { take(); yield whitespace().not(); }
            case 'n' -> { take(); yield CodePoints.of('\n'); }
            case 't' -> { take(); yield CodePoints.of('\t'); }
            case 'r' -> { take(); yield CodePoints.of('\r'); }
            case 'f' -> { take(); yield CodePoints.of('\f'); }
            case 'a' -> { take(); yield CodePoints.of(0x07); }
            case 'e' -> { take(); yield CodePoints.of(0x1B); }
            case '0' -> { take(); yield CodePoints.of(octal()); }
            case 'x' -> { take(); yield CodePoints.of(hex()); }
            case 'u' -> { take(); yield CodePoints.of(unicodeEscape()); }
            case 'p', 'P' -> throw new Refused(PatternRead.Unsupported.A_CHARACTER_PROPERTY);
            case 'b', 'B', 'A', 'z', 'Z', 'G', 'R' ->
                    throw new Refused(PatternRead.Unsupported.A_BOUNDARY);
            case 'Q', 'E' -> throw new Refused(PatternRead.Unsupported.A_QUOTATION);
            case 'k' -> throw new Refused(PatternRead.Unsupported.A_BACK_REFERENCE);
            case 'c' -> throw new Refused(PatternRead.Unsupported.AN_ESCAPE_THIS_DOES_NOT_READ);
            case '1', '2', '3', '4', '5', '6', '7', '8', '9' ->
                    throw new Refused(PatternRead.Unsupported.A_BACK_REFERENCE);
            default -> {
                // An escaped literal — `\.`, `\+`, `\\`, `\-`. A letter with no meaning is refused
                // rather than read as itself, since Java refuses it too and reading it would accept
                // a pattern the engine does not.
                if (Character.isLetter(kind)) {
                    throw new Refused(PatternRead.Unsupported.AN_ESCAPE_THIS_DOES_NOT_READ);
                }
                yield CodePoints.of(literal());
            }
        };
    }

    private static CodePoints digits() {
        return CodePoints.between('0', '9');
    }

    private static CodePoints word() {
        return CodePoints.between('a', 'z').or(CodePoints.between('A', 'Z'))
                .or(digits()).or(CodePoints.of('_'));
    }

    /** What Java calls whitespace without a flag: a space, a tab, a line feed, a vertical tab, a
     *  form feed and a carriage return. */
    private static CodePoints whitespace() {
        return CodePoints.of(' ').or(CodePoints.between('\t', '\r'));
    }

    // --- numbers and symbols -----------------------------------------------------------------------

    /** `\xHH`, or `\x{H...}` for a symbol past the basic plane. */
    private int hex() {
        if (peek() == '{') {
            take();
            int value = 0;
            int digits = 0;
            while (!done() && peek() != '}') {
                int digit = Character.digit(take(), 16);
                if (digit < 0) {
                    throw new Refused(PatternRead.Unsupported.AN_ESCAPE_THIS_DOES_NOT_READ);
                }
                value = value * 16 + digit;
                digits++;
                if (value > CodePoints.LAST) {
                    throw new Refused(PatternRead.Unsupported.AN_ESCAPE_THIS_DOES_NOT_READ);
                }
            }
            expect('}');
            if (digits == 0) {
                throw new Refused(PatternRead.Unsupported.AN_ESCAPE_THIS_DOES_NOT_READ);
            }
            return value;
        }
        return fixedHex(2);
    }

    /**
     * The symbol a {@code \\u} escape spells, two of them making one where they pair.
     *
     * <p>Java's engine reads a pattern as units before it reads it as symbols, so a high escape
     * followed by a low one is the one supplementary symbol they encode — {@code \\uD800\\uDC00}
     * accepts U+10000 and accepts neither half on its own. Read as two symbols, the same pattern
     * would name the two halves and not the character, which is a different set of strings under
     * the same spelling.
     *
     * <p>And a set that no walk here could even ask about. What a machine is walked over is code
     * points, so a step over half a pair is a step nothing takes: the language would hold a string
     * its own membership test refuses, and the shortest string it could name would be one it does
     * not have.
     *
     * <p>A high escape with nothing to pair with is the symbol it spells and stays one. That is
     * what the engine does with it, and a lone surrogate is a symbol a machine may hold.
     */
    private int unicodeEscape() {
        int first = fixedHex(4);
        if (!Character.isHighSurrogate((char) first) || peek() != '\\') {
            return first;
        }
        int mark = at;
        take();
        if (peek() != 'u') {
            at = mark;
            return first;
        }
        take();
        int second = fixedHex(4);
        if (!Character.isLowSurrogate((char) second)) {
            at = mark;
            return first;
        }
        return Character.toCodePoint((char) first, (char) second);
    }

    private int fixedHex(int digits) {
        int value = 0;
        for (int i = 0; i < digits; i++) {
            if (done()) {
                throw new Refused(PatternRead.Unsupported.AN_ESCAPE_THIS_DOES_NOT_READ);
            }
            int digit = Character.digit(take(), 16);
            if (digit < 0) {
                throw new Refused(PatternRead.Unsupported.AN_ESCAPE_THIS_DOES_NOT_READ);
            }
            value = value * 16 + digit;
        }
        return value;
    }

    /** `\0n`, `\0nn` or `\0mnn` — up to three octal digits after the zero. */
    private int octal() {
        int value = 0;
        int digits = 0;
        while (digits < 3 && !done() && peek() >= '0' && peek() <= '7') {
            value = value * 8 + (take() - '0');
            digits++;
        }
        if (digits == 0 || value > 0xFF) {
            throw new Refused(PatternRead.Unsupported.AN_ESCAPE_THIS_DOES_NOT_READ);
        }
        return value;
    }

    /**
     * The symbol written here, which is a whole code point where the source holds a pair.
     *
     * <p>A pattern written with a character past the basic plane holds it as two units, and a reader
     * taking one unit at a time would build a language of halves. Where the source holds half a pair
     * on its own, that half is the symbol — which is what the engine does with it.
     */
    private int literal() {
        if (done()) {
            throw new Refused(PatternRead.Unsupported.SOMETHING_UNCLOSED);
        }
        int symbol = regex.codePointAt(at);
        at += Character.charCount(symbol);
        return symbol;
    }

    /** A repetition's count, which is a whole number this can hold. */
    private int count() {
        int value = 0;
        int digits = 0;
        while (!done() && peek() >= '0' && peek() <= '9') {
            value = value * 10 + (take() - '0');
            digits++;
            if (value > Integer.MAX_VALUE / 16) {
                throw new Refused(PatternRead.Unsupported.A_COUNT_THIS_CANNOT_READ);
            }
        }
        if (digits == 0) {
            throw new Refused(PatternRead.Unsupported.A_COUNT_THIS_CANNOT_READ);
        }
        return value;
    }

    // --- walking -----------------------------------------------------------------------------------

    private void deeper() {
        if (++depth > DEEPEST) {
            throw new Refused(PatternRead.Unsupported.NESTED_TOO_DEEPLY);
        }
    }

    private void shallower() {
        depth--;
    }

    private boolean done() {
        return at >= regex.length();
    }

    /** The unit here, or {@code 0} at the end. Read as a unit rather than as a symbol, because what
     *  the grammar branches on is punctuation and all of it is one unit wide. */
    private char peek() {
        return done() ? 0 : regex.charAt(at);
    }

    private char take() {
        if (done()) {
            throw new Refused(PatternRead.Unsupported.SOMETHING_UNCLOSED);
        }
        return regex.charAt(at++);
    }

    private void expect(char c) {
        if (peek() != c) {
            throw new Refused(PatternRead.Unsupported.SOMETHING_UNCLOSED);
        }
        take();
    }

    /** What a construct outside the subset raises, carried to the one place that answers. */
    private static final class Refused extends RuntimeException {

        private static final long serialVersionUID = 1L;

        private final transient PatternRead.Unsupported why;

        Refused(PatternRead.Unsupported why) {
            super(null, null, false, false);
            this.why = why;
        }
    }
}
