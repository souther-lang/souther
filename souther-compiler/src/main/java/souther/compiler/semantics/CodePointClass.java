package souther.compiler.semantics;

import net.unit8.notation199x.WhiteSpace;
import net.unit8.notation199x.pattern.CodePoints;

/**
 * Which code points of a string are counted by {@link NumericTerm.CodePointClassCount}.
 *
 * <p>The classes the readings that need a count come to. What a string holds besides whitespace is
 * what is left of it once it is trimmed; what it holds besides whitespace and one separator is what
 * the pieces a split by that separator leaves hold between them. Whitespace is the one alphabet
 * {@code String.trim} and {@code String.words} share (spec §string-whitespace), so a count of what
 * is not in it is a count the run time agrees with. And a set of code points one character is read
 * to be one of — the characters a pattern of one symbol accepts, together with what else was
 * stated of the same character — is counted as that set ({@link OneOf}).
 *
 * <p>Not a predicate a program writes. A closure counted by is any function and nothing here reads
 * one; these are the classes this compiler can say exactly what a string must hold for.
 *
 * <p>One class has one spelling: a set that is one of the named classes is that class ({@link
 * #of}), so that two readings of one set are equal.
 */
public sealed interface CodePointClass {

    /** Whether {@code codePoint} is one the class counts. */
    boolean contains(int codePoint);

    /** The code points the class counts. */
    CodePoints held();

    /**
     * The class counting exactly {@code held}: the named class where it is one, and otherwise the
     * set itself.
     */
    static CodePointClass of(CodePoints held) {
        CodePointClass named = named(held);
        return named != null ? named : new OneOf(held);
    }

    /** The named class counting exactly {@code held}, or null where none does. */
    private static CodePointClass named(CodePoints held) {
        CodePoints notWhitespace = NotWhitespace.Held.SET;
        if (held.equals(notWhitespace)) {
            return new NotWhitespace();
        }
        CodePoints left = notWhitespace.less(held);
        return held.less(notWhitespace).isEmpty() && left.size() == 1
                ? new NotWhitespaceNorEqualTo(left.least()) : null;
    }

    /** The code points that are not whitespace. */
    record NotWhitespace() implements CodePointClass {

        @Override
        public boolean contains(int codePoint) {
            return !WhiteSpace.contains(codePoint);
        }

        @Override
        public CodePoints held() {
            return Held.SET;
        }

        @Override
        public String toString() {
            return "not whitespace";
        }

        /**
         * The code points that are not whitespace, worked out the first time the set is asked
         * for: every code point is asked whether it is whitespace, and a class that is only
         * asked of one code point at a time never needs it.
         */
        private static final class Held {

            private static final CodePoints SET = notWhitespace();

            /** Every code point but those with the {@code White_Space} property. */
            private static CodePoints notWhitespace() {
                CodePoints whitespace = CodePoints.NONE;
                for (int codePoint = 0; codePoint <= CodePoints.LAST; codePoint++) {
                    if (!CodePoints.isSurrogate(codePoint) && WhiteSpace.contains(codePoint)) {
                        whitespace = whitespace.or(CodePoints.of(codePoint));
                    }
                }
                return whitespace.not();
            }
        }
    }

    /** The code points that are neither whitespace nor {@code separator}. */
    record NotWhitespaceNorEqualTo(int separator) implements CodePointClass {

        public NotWhitespaceNorEqualTo {
            boolean isSurrogate =
                    separator >= Character.MIN_SURROGATE && separator <= Character.MAX_SURROGATE;
            if (!Character.isValidCodePoint(separator) || isSurrogate) {
                throw new IllegalArgumentException(separator + " is no code point a string holds");
            }
        }

        @Override
        public boolean contains(int codePoint) {
            return codePoint != separator && !WhiteSpace.contains(codePoint);
        }

        @Override
        public CodePoints held() {
            return NotWhitespace.Held.SET.less(CodePoints.of(separator));
        }

        @Override
        public String toString() {
            return "not whitespace nor U+%X".formatted(separator);
        }
    }

    /**
     * The code points of {@code held}, a set that is none of the named classes ({@link #of}).
     */
    record OneOf(CodePoints held) implements CodePointClass {

        public OneOf {
            if (held == null) {
                throw new IllegalArgumentException("a class counts some set of code points");
            }
            if (named(held) != null) {
                throw new IllegalArgumentException(held + " is a named class, spelled as that");
            }
        }

        @Override
        public boolean contains(int codePoint) {
            return held.has(codePoint);
        }

        @Override
        public String toString() {
            return "one of " + held;
        }
    }
}
