package souther.compiler.semantics;

import net.unit8.notation199x.WhiteSpace;

/**
 * Which code points of a string are counted by {@link NumericTerm.CodePointClassCount}.
 *
 * <p>Two classes and no more, because the readings that need a count are two: what a string holds
 * besides whitespace, which is what is left of it once it is trimmed, and what it holds besides
 * whitespace and one separator, which is what the pieces a split by that separator leaves hold
 * between them. Whitespace is the one alphabet {@code String.trim} and {@code String.words} share
 * (spec §string-whitespace), so a count of what is not in it is a count the run time agrees with.
 *
 * <p>Not a predicate a program writes. A closure counted by is any function and nothing here reads
 * one; these are the classes this compiler can say exactly what a string must hold for.
 */
public sealed interface CodePointClass {

    /** Whether {@code codePoint} is one the class counts. */
    boolean contains(int codePoint);

    /** The code points that are not whitespace. */
    record NotWhitespace() implements CodePointClass {

        @Override
        public boolean contains(int codePoint) {
            return !WhiteSpace.contains(codePoint);
        }

        @Override
        public String toString() {
            return "not whitespace";
        }
    }

    /** The code points that are neither whitespace nor {@code separator}. */
    record NotWhitespaceNorEqualTo(int separator) implements CodePointClass {

        public NotWhitespaceNorEqualTo {
            if (!Character.isValidCodePoint(separator)
                    || separator >= Character.MIN_SURROGATE && separator <= Character.MAX_SURROGATE) {
                throw new IllegalArgumentException(separator + " is no code point a string holds");
            }
        }

        @Override
        public boolean contains(int codePoint) {
            return codePoint != separator && !WhiteSpace.contains(codePoint);
        }

        @Override
        public String toString() {
            return "not whitespace nor U+%X".formatted(separator);
        }
    }
}
