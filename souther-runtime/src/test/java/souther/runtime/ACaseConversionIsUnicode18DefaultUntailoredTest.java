package souther.runtime;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertEquals;

/**
 * ADR-0119: {@code lowercase}/{@code uppercase} are Unicode 18.0.0's default case conversion,
 * untailored — full mapping, including the one-to-many expansions {@code SpecialCasing.txt} states
 * and the context-dependent {@code Final_Sigma} condition, with no locale carried at all.
 *
 * <p>Every case here would pass under the {@code String.toLowerCase()}/{@code toUpperCase()} this
 * replaced only by accident, if at all: the first two distinguish full mapping from simple; the
 * {@code Final_Sigma} cases distinguish "preceded/followed by a Cased code point" from a naive
 * "previous/next character", including the one code point that is both {@code Cased} and
 * {@code Case_Ignorable}; the Turkish-tailoring case distinguishes untailored from the JVM's
 * default-locale-dependent behaviour; and the last asserts the Unicode 18.0.0 contract directly,
 * on a case pair this JVM's own casing does not currently answer — motivation for the contract,
 * not something the assertion depends on.
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
    void finalSigmaSkipsCaseIgnorableCodePointsAfterTheSigma() {
        // APOSTROPHE (U+0027) is Case_Ignorable: skipped, sigma is still at the end of a cased run.
        assertEquals("ος'", Strings.lowercase("ΟΣ'"));
    }

    @Test
    void finalSigmaSkipsCaseIgnorableCodePointsBeforeTheSigma() {
        // The apostrophe sits between the cased letter and the sigma; skipped the same way.
        assertEquals("ο'ς", Strings.lowercase("Ο'Σ"));
    }

    @Test
    void aCasedLetterAcrossAnIgnorableAfterTheSigmaStillDeniesTheFinalForm() {
        // Skipping the apostrophe still reaches a Cased letter, so this is not the end of the run.
        assertEquals("οσ'α", Strings.lowercase("ΟΣ'Α"));
    }

    @Test
    void aCodePointThatIsBothCasedAndCaseIgnorableDoesNotSatisfyPrecededByCased() {
        // U+0345 (COMBINING GREEK YPOGEGRAMMENI) is both Cased and Case_Ignorable. Unicode's
        // Final_Sigma "Before C" pattern is possessive over Case_Ignorable* — it consumes U+0345
        // as the skipped run before ever asking whether what it skipped was Cased — so a sigma
        // right after it is not preceded by a cased letter, and takes the non-final form.
        assertEquals("ͅσ", Strings.lowercase("ͅΣ"));
    }

    @Test
    void uppercaseDoesNotApplyTurkishDotlessITailoring() {
        assertEquals("I", Strings.uppercase("i"));
        assertEquals("i", Strings.lowercase("I"));
    }

    @Test
    void unicode18VersionSentinelCasePair() {
        // U+AB4B (LATIN SMALL LETTER SCRIPT R) to U+AB6C is a genuine Unicode 18.0.0 case pair.
        // What this asserts is the language contract alone: this JVM's own casing tables happen
        // not to know the pair yet (see ADR-0119's Context for that fact and why it matters), but
        // that is motivation, not something this test depends on — it must keep passing on a future
        // JDK whose own tables catch up, without needing an update here.
        String scriptR = new String(Character.toChars(0xAB4B));
        String capitalScriptR = new String(Character.toChars(0xAB6C));

        assertEquals(capitalScriptR, Strings.uppercase(scriptR));
    }
}
