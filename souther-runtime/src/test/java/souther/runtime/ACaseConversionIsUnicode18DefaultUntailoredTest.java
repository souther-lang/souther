package souther.runtime;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * ADR-0119: {@code lowercase}/{@code uppercase} are Unicode 18.0.0's default case conversion,
 * untailored — full mapping, including the one-to-many expansions {@code SpecialCasing.txt} states
 * and the context-dependent {@code Final_Sigma} condition, with no locale carried at all.
 *
 * <p>Every case here would pass under the {@code String.toLowerCase()}/{@code toUpperCase()} this
 * replaced only by accident, if at all: the first two distinguish full mapping from simple, the
 * next two distinguish untailored from the JVM's default-locale-dependent behaviour, and the last
 * is a Unicode version pin — a case pair this JVM's own {@code Character}/{@code String} casing
 * does not know, so a regression to the JDK table fails it even though it never touches a locale.
 */
class ACaseConversionIsUnicode18DefaultUntailoredTest {

    @Test
    void uppercaseExpandsGermanSharpSToTwoLetters() {
        assertEquals("STRASSE", Strings.uppercase("straße"));
    }

    @Test
    void lowercaseExpandsTurkishCapitalIWithDotToTwoCodePoints() {
        // Full mapping, unconditional (not the Turkish-locale-tailored single "i" SpecialCasing.txt
        // also lists, and which this contract deliberately does not carry).
        assertEquals("i̇", Strings.lowercase("İ"));
    }

    @Test
    void lowercaseGreekCapitalSigmaIsContextSensitive() {
        assertEquals("ος", Strings.lowercase("ΟΣ"), "sigma ending a cased run takes the final form");
        assertEquals("οσα", Strings.lowercase("ΟΣΑ"), "sigma followed by another cased letter does not");
        assertEquals("σ", Strings.lowercase("Σ"), "sigma with nothing cased before it is not final either");
    }

    @Test
    void finalSigmaSkipsCaseIgnorableCodePointsOnBothSides() {
        // APOSTROPHE (U+0027) is Case_Ignorable, so it does not break "preceded by Cased".
        assertEquals("ος'", Strings.lowercase("ΟΣ'"));
    }

    @Test
    void uppercaseDoesNotApplyTurkishDotlessITailoring() {
        assertEquals("I", Strings.uppercase("i"));
        assertEquals("i", Strings.lowercase("I"));
    }

    @Test
    void unicode18AddedACasePairThisJvmsOwnCasingDoesNotKnow() {
        String scriptR = new String(Character.toChars(0xAB4B));
        String capitalScriptR = new String(Character.toChars(0xAB6C));

        assertEquals(capitalScriptR, Strings.uppercase(scriptR));
        assertNotEquals(capitalScriptR, scriptR.toUpperCase(java.util.Locale.ROOT),
                "this JVM's own String uppercasing must still not know this pair, or the sentinel"
                        + " no longer tells a JDK-table regression apart from the real thing");
    }
}
