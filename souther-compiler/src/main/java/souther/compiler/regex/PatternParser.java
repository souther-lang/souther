package souther.compiler.regex;

import java.util.ArrayList;
import java.util.List;

/**
 * The reader of Souther's pattern language (spec §string-patterns), and the only one.
 *
 * <p>What this reads is a pattern and what it refuses is not one. The checker asks this whether a
 * {@code String.matches} pattern is one, and what it hands on is the {@link PatternMeaning}; the
 * analysis, the compiler's folds and every output lower that. None of them reads the text, so a
 * construct this learns is learned by all of them at once, and there is no second reader whose
 * answer could differ.
 *
 * <p>Nothing here chooses a value. What one string of the language would be is a question for
 * whatever holds the language; a reader that answered it while parsing is the arrangement that lost
 * the second arm of every choice and the ceiling of every repetition.
 */
public final class PatternParser {

    /**
     * How deep a pattern may be written.
     *
     * <p>A limit of this compiler and not of the language. The reading is recursive, and so is every
     * walk over what it reads — the machines built from it and what an output lowers it to — so what
     * bounds them is the stack. Past this the answer is {@link PatternRead.TooDeep} rather than a
     * stack overflow somewhere later in a compile.
     */
    public static final int DEEPEST = 200;

    private final String regex;
    private int at;
    private int depth;
    /** Where the construct being read begins, which is what a refusal quotes. */
    private int construct;

    private PatternParser(String regex) {
        this.regex = regex;
        this.at = 0;
        this.depth = 0;
        this.construct = 0;
    }

    /** What {@code regex} means, or what makes it no pattern, or that it is deeper than this reads. */
    public static PatternRead read(String regex) {
        if (regex == null) {
            throw new IllegalArgumentException("a pattern is some string");
        }
        PatternParser reader = new PatternParser(regex);
        try {
            WrittenPattern written = reader.alternation();
            if (!reader.done()) {
                // A bracket closing nothing, which is what is left when the reading of a choice
                // stops before the end.
                return new PatternRead.Refused(PatternRead.Refusal.SOMETHING_UNCLOSED, reader.at,
                        regex.substring(reader.at, reader.at + 1));
            }
            // Every anchor has to come to something, and what it comes to is settled by where it
            // stands rather than by how it is written — which is known now that the whole of the
            // pattern is.
            PatternMeaning meaning = Anchors.placed(written);
            if (meaning == null) {
                return new PatternRead.Refused(PatternRead.Refusal.AN_ANCHOR_THIS_CANNOT_PLACE, 0,
                        regex);
            }
            return new PatternRead.Read(meaning);
        } catch (Refused refused) {
            int to = Math.min(regex.length(), Math.max(refused.to, refused.from));
            return new PatternRead.Refused(refused.why, refused.from,
                    regex.substring(refused.from, to));
        } catch (TooDeep _) {
            return new PatternRead.TooDeep(DEEPEST);
        }
    }

    // --- the grammar ------------------------------------------------------------------------------

    private WrittenPattern alternation() {
        List<WrittenPattern> arms = new ArrayList<>();
        arms.add(sequence());
        while (peek() == '|') {
            take();
            arms.add(sequence());
        }
        return arms.size() == 1 ? arms.get(0) : new WrittenPattern.EitherOf(arms);
    }

    private WrittenPattern sequence() {
        List<WrittenPattern> parts = new ArrayList<>();
        while (!done() && peek() != '|' && peek() != ')') {
            WrittenPattern one = quantified();
            // A group of nothing is nothing, and is left out so that one written pattern has one
            // tree. An anchor is not one of those: where it stands is what decides what it comes
            // to, so dropping it here would be answering that question with the one place that
            // cannot see the answer.
            if (!(one instanceof WrittenPattern.Meant(PatternMeaning.Nothing _))) {
                parts.add(one);
            }
        }
        return switch (parts.size()) {
            case 0 -> new WrittenPattern.Meant(new PatternMeaning.Nothing());
            case 1 -> parts.get(0);
            default -> new WrittenPattern.InTurn(parts);
        };
    }

    private WrittenPattern quantified() {
        WrittenPattern one = atom();
        int least;
        int most;
        construct = at;
        switch (peek()) {
            case '?' -> { take(); least = 0; most = 1; }
            case '*' -> { take(); least = 0; most = PatternMeaning.Repeated.NO_CEILING; }
            case '+' -> { take(); least = 1; most = PatternMeaning.Repeated.NO_CEILING; }
            case '{' -> {
                take();
                least = count();
                most = least;
                if (peek() == ',') {
                    take();
                    most = peek() == '}' ? PatternMeaning.Repeated.NO_CEILING : count();
                }
                expect('}');
                if (most != PatternMeaning.Repeated.NO_CEILING && most < least) {
                    throw refused(PatternRead.Refusal.A_COUNT_THIS_CANNOT_READ);
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
            // string. Which strings it accepts is a fact about a matcher, and the language has none.
            take();
            throw refused(PatternRead.Refusal.A_POSSESSIVE_REPETITION);
        }
        return new WrittenPattern.Repeated(one, least, most);
    }

    private WrittenPattern atom() {
        construct = at;
        char c = peek();
        return switch (c) {
            case '(' -> group();
            case '[' -> {
                take();
                yield symbols(characterClass());
            }
            case '\\' -> {
                take();
                yield symbols(escaped());
            }
            case '.' -> {
                take();
                // Every symbol but the line terminators. Written as a difference rather than as a
                // rule of its own, so that a negated class beside it — which does not leave them
                // out — is the same algebra with a different set taken away.
                yield symbols(CodePoints.EVERYTHING.less(CodePoints.LINE_TERMINATORS));
            }
            case '^', '$' -> {
                boolean end = peek() == '$';
                take();
                yield new WrittenPattern.Anchor(end);
            }
            // A brace that begins no count. Read as an ordinary character it would be a pattern
            // meaning one thing here and a count wherever a digit followed it.
            case '{' -> {
                take();
                throw refused(PatternRead.Refusal.A_COUNT_THIS_CANNOT_READ);
            }
            case '*', '+', '?' -> {
                take();
                throw refused(PatternRead.Refusal.SOMETHING_UNCLOSED);
            }
            case 0 -> throw refused(PatternRead.Refusal.SOMETHING_UNCLOSED);
            default -> symbols(CodePoints.of(literal()));
        };
    }

    private static WrittenPattern symbols(CodePoints held) {
        return new WrittenPattern.Meant(new PatternMeaning.Symbols(held));
    }

    /** A group, which this reads only where it says nothing about the match. */
    private WrittenPattern group() {
        expect('(');
        if (peek() == '?') {
            take();
            // `(?:` and nothing else. A lookaround, a named group and a flag group each say
            // something about where a match sits or how it is walked, which no set of strings holds.
            if (peek() != ':') {
                take();
                throw refused(PatternRead.Refusal.A_GROUP_ABOUT_THE_MATCH);
            }
            take();
        }
        deeper();
        WrittenPattern inside = alternation();
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
            construct = at;
            if (peek() == '[') {
                take();
                throw refused(PatternRead.Refusal.A_CLASS_OF_CLASSES);
            }
            if (peek() == '&' && at + 1 < regex.length() && regex.charAt(at + 1) == '&') {
                at += 2;
                throw refused(PatternRead.Refusal.A_CLASS_OF_CLASSES);
            }
            held = held.or(classMember());
        }
        expect(']');
        if (held.isEmpty()) {
            throw refused(PatternRead.Refusal.SOMETHING_UNCLOSED);
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
                throw refused(PatternRead.Refusal.AN_ESCAPE_THIS_DOES_NOT_READ);
            }
            if (upper.least() < member.least()) {
                throw refused(PatternRead.Refusal.A_COUNT_THIS_CANNOT_READ);
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
            throw refused(PatternRead.Refusal.AN_ESCAPE_THIS_DOES_NOT_READ);
        }
        char kind = peek();
        return switch (kind) {
            // The shorthands, as the language defines them: the digits are the ten ASCII ones, a
            // word character is ASCII with the underscore, and the whitespace is six characters.
            case 'd' -> { take(); yield CodePoints.DIGITS; }
            case 'D' -> { take(); yield CodePoints.DIGITS.not(); }
            case 'w' -> { take(); yield CodePoints.WORD; }
            case 'W' -> { take(); yield CodePoints.WORD.not(); }
            case 's' -> { take(); yield CodePoints.SPACES; }
            case 'S' -> { take(); yield CodePoints.SPACES.not(); }
            case 'n' -> { take(); yield CodePoints.of('\n'); }
            case 't' -> { take(); yield CodePoints.of('\t'); }
            case 'r' -> { take(); yield CodePoints.of('\r'); }
            case 'f' -> { take(); yield CodePoints.of('\f'); }
            case 'a' -> { take(); yield CodePoints.of(0x07); }
            case 'e' -> { take(); yield CodePoints.of(0x1B); }
            case '0' -> { take(); yield CodePoints.of(octal()); }
            case 'x' -> { take(); yield CodePoints.of(spelled(PatternEscapes.hex(regex, at))); }
            case 'u' -> { take(); yield CodePoints.of(spelled(PatternEscapes.unicode(regex, at))); }
            case 'p', 'P' -> throw refusedAfter(PatternRead.Refusal.A_CHARACTER_PROPERTY);
            case 'b', 'B', 'A', 'z', 'Z', 'G', 'R' -> throw refusedAfter(PatternRead.Refusal.A_BOUNDARY);
            case 'Q', 'E' -> throw refusedAfter(PatternRead.Refusal.A_QUOTATION);
            case 'k', '1', '2', '3', '4', '5', '6', '7', '8', '9' ->
                    throw refusedAfter(PatternRead.Refusal.A_BACK_REFERENCE);
            default -> {
                // An escaped literal — `\.`, `\+`, `\\`, `\-`. A letter with no meaning is refused
                // rather than read as itself: read as itself, a letter one day given a meaning
                // would change which strings an old pattern accepts.
                if (Character.isLetter(kind)) {
                    throw refusedAfter(PatternRead.Refusal.AN_ESCAPE_THIS_DOES_NOT_READ);
                }
                yield CodePoints.of(literal());
            }
        };
    }

    /** The refusal of the escape whose kind is the unit here, quoting it with that unit. */
    private Refused refusedAfter(PatternRead.Refusal why) {
        take();
        return refused(why);
    }

    // --- numbers and symbols -----------------------------------------------------------------------

    /**
     * The symbol a {@code \x} or {@code \\u} escape spells ({@link PatternEscapes}), the reading
     * moved past it.
     *
     * <p>A {@code \\u} pair is the one character it encodes: read as two symbols,
     * {@code \\uD800\\uDC00} would name the two halves and not U+10000, a different set of strings
     * under the same spelling. A surrogate on its own is no symbol, since no {@code String} holds
     * one, and is refused.
     */
    private int spelled(PatternEscapes.Spelled escape) {
        if (escape == null) {
            throw refused(PatternRead.Refusal.AN_ESCAPE_THIS_DOES_NOT_READ);
        }
        at = escape.end();
        if (CodePoints.isSurrogate(escape.symbol())) {
            throw refused(PatternRead.Refusal.A_CHARACTER_NO_STRING_HOLDS);
        }
        return escape.symbol();
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
            throw refused(PatternRead.Refusal.AN_ESCAPE_THIS_DOES_NOT_READ);
        }
        return value;
    }

    /**
     * The symbol written here, which is a whole code point where the source holds a pair.
     *
     * <p>A pattern written with a character past the basic plane holds it as two units, and a reader
     * taking one unit at a time would build a language of halves. The pattern is a {@code String},
     * so it holds no half of a pair on its own.
     */
    private int literal() {
        if (done()) {
            throw refused(PatternRead.Refusal.SOMETHING_UNCLOSED);
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
                throw refused(PatternRead.Refusal.A_COUNT_THIS_CANNOT_READ);
            }
        }
        if (digits == 0) {
            throw refused(PatternRead.Refusal.A_COUNT_THIS_CANNOT_READ);
        }
        return value;
    }

    // --- walking -----------------------------------------------------------------------------------

    private void deeper() {
        if (++depth > DEEPEST) {
            throw new TooDeep();
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
            throw refused(PatternRead.Refusal.SOMETHING_UNCLOSED);
        }
        return regex.charAt(at++);
    }

    private void expect(char c) {
        if (peek() != c) {
            // What is missing is a closing, and where it was looked for is what an author is sent
            // to — not the construct it would have closed, which may be far behind.
            construct = at;
            throw refused(PatternRead.Refusal.SOMETHING_UNCLOSED);
        }
        take();
    }

    /** The refusal of the construct being read, quoting it from where it began to where the reading
     *  stopped. */
    private Refused refused(PatternRead.Refusal why) {
        return new Refused(why, construct, at);
    }

    /** What a pattern that is no pattern raises, carried to the one place that answers. */
    private static final class Refused extends RuntimeException {

        private static final long serialVersionUID = 1L;

        private final transient PatternRead.Refusal why;
        private final int from;
        private final int to;

        Refused(PatternRead.Refusal why, int from, int to) {
            super(null, null, false, false);
            this.why = why;
            this.from = from;
            this.to = to;
        }
    }

    /** What a pattern written past {@link #DEEPEST} raises. */
    private static final class TooDeep extends RuntimeException {

        private static final long serialVersionUID = 1L;

        TooDeep() {
            super(null, null, false, false);
        }
    }
}
