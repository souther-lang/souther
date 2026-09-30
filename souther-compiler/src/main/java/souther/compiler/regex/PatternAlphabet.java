package souther.compiler.regex;

import souther.compiler.text.UnicodeProperty;

import java.util.Set;

/**
 * The characters a backslash before which the pattern language keeps for an escape: the letters and
 * the decimal digits, General_Category {@code L} and {@code Nd}, against the Unicode version the
 * data names (spec §string-patterns).
 *
 * <p>What a pattern is is part of what a compiled module promises, since a published helper's body
 * travels as source and is read again by the importing compiler. Asked of the running JDK, the
 * answer would move with whatever Unicode version that JDK carries, and a body one compiler read
 * another would refuse. The version is the one the language fixes for what a {@code String} holds,
 * because the characters of a pattern are the scalar values of a {@code String}.
 */
final class PatternAlphabet {

    private PatternAlphabet() {}

    /** An excerpt of {@code DerivedGeneralCategory.txt}: its header and the lines of the values
     *  read here. */
    private static final String RESOURCE = "pattern-escape-alphabet.txt";

    private static final Set<String> KEPT = Set.of("Lu", "Ll", "Lt", "Lm", "Lo", "Nd");

    private static final UnicodeProperty KEPT_AFTER_A_BACKSLASH = UnicodeProperty.read(
            PatternAlphabet.class, RESOURCE, "DerivedGeneralCategory", KEPT, KEPT);

    /** Whether a backslash before {@code codePoint} is kept for an escape: a letter or a decimal
     *  digit. */
    static boolean isKeptAfterABackslash(int codePoint) {
        return KEPT_AFTER_A_BACKSLASH.has(codePoint);
    }

    /** The Unicode version the classification is read against. */
    static String unicodeVersion() {
        return KEPT_AFTER_A_BACKSLASH.unicodeVersion();
    }
}
