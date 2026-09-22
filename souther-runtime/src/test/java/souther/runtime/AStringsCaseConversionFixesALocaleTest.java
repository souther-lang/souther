package souther.runtime;

import org.junit.jupiter.api.Test;

import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * {@code Strings.lowercase}/{@code uppercase} fix {@link Locale#ROOT} (spec §string-case,
 * ADR-0119) rather than reaching {@code String}'s no-argument {@code toLowerCase()}/
 * {@code toUpperCase()}, which read {@link Locale#getDefault()} — a JVM starting under a Turkish
 * default locale would otherwise make the same Souther program answer differently. This does not
 * mutate the JVM's actual default locale (parallel forks share it); it compares {@code Strings}'
 * answer against what the Turkish-locale overload would have answered, which is what a
 * default-locale-dependent implementation could have returned.
 */
class AStringsCaseConversionFixesALocaleTest {

    private static final Locale TURKISH = Locale.forLanguageTag("tr");

    @Test
    void aPlainIUppercasesToPlainIRegardlessOfTurkishLocaleConventions() {
        assertEquals("I", Strings.uppercase("i"));
        // What a default-locale-dependent toUpperCase() could have answered under a Turkish
        // default ("İ", dotted capital I) — Strings.uppercase must not agree with it.
        assertNotEquals("i".toUpperCase(TURKISH), Strings.uppercase("i"));
    }

    @Test
    void aPlainCapitalILowercasesToPlainIRegardlessOfTurkishLocaleConventions() {
        assertEquals("i", Strings.lowercase("I"));
        assertNotEquals("I".toLowerCase(TURKISH), Strings.lowercase("I"));
    }

    @Test
    void bothOperationsUseTheRootLocaleDirectly() {
        assertEquals("i".toUpperCase(Locale.ROOT), Strings.uppercase("i"));
        assertEquals("I".toLowerCase(Locale.ROOT), Strings.lowercase("I"));
    }
}
