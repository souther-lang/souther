package souther.compiler.diag;

import org.junit.jupiter.api.Test;

import static org.junit.jupiter.api.Assertions.assertThrows;

/**
 * Rendering a message takes a language, and "none" is not one of them.
 *
 * <p>No locale used to mean the default one, which put the default back within reach of every
 * caller: a site with no reader to resolve for could pass nothing and be answered out of the
 * language chosen for readers who named none — the same mistake {@code defaultLocale()} being
 * public allowed, spelled differently and invisible to a scan for the ways a locale is picked.
 *
 * <p>So the two ways in refuse it. A caller either resolved a language for a reader or is building
 * text that has no reader, and the second has {@link DiagnosticRenderer#legacyBody} to build it
 * with. Neither is a caller with a language it did not decide.
 */
class AskingForAMessageWithoutALanguageIsRefusedTest {

    private static final String KEY = "example.the-row-reached-an-unreachable-point";

    @Test
    void aMessageLookupWithNoLanguageIsRefused() {
        assertThrows(NullPointerException.class, () -> Messages.get(KEY, null, "why"));
    }

    @Test
    void askingWhetherTheCatalogDefinesAKeyWithNoLanguageIsRefused() {
        assertThrows(NullPointerException.class, () -> Messages.has(KEY, null));
    }

    @Test
    void renderingABodyWithNoLanguageIsRefused() {
        Diagnostic d = Diagnostic.of(DiagnosticCode.E1911, KEY).args("why").build();

        assertThrows(NullPointerException.class, () -> DiagnosticRenderer.body(d, null));
    }
}
