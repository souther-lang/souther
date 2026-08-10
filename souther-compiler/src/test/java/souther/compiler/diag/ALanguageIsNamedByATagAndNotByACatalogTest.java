package souther.compiler.diag;

import org.junit.jupiter.api.Test;

import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertFalse;
import static org.junit.jupiter.api.Assertions.assertNull;
import static org.junit.jupiter.api.Assertions.assertTrue;

/**
 * A language is named by a tag. Whether this toolchain has a catalog for it is a separate question,
 * and the answer to it is which language the messages come back in — never whether the reader was
 * allowed to ask.
 *
 * <p>The two were one question by accident. {@link Locale#forLanguageTag} is written to be tolerant:
 * handed a subtag it cannot read it keeps the well-formed part in front of it and drops the rest, so
 * {@code en-!!} arrived as English and {@code !!} as a locale with no language in it, and both were
 * answered in English — the same answer a reader who named nothing gets. Every way of getting that
 * wrong ended in the same place, which is why nothing showed it.
 */
class ALanguageIsNamedByATagAndNotByACatalogTest {

    @Test
    void aTagNamesALanguage() {
        for (String tag : List.of("ja", "en", "fr", "fr-CA", "en-x-souther")) {
            assertTrue(Messages.namesALanguage(tag), tag);
        }
    }

    /**
     * Including the ones no catalog answers. A tag that names a language nobody has translated this
     * into is a reader saying which language they read, which is the thing the resolution is for.
     */
    @Test
    void aLanguageWithNoCatalogIsStillNamed() {
        for (String tag : List.of("fr", "zz", "und", "x-souther")) {
            assertTrue(Messages.namesALanguage(tag), tag);
        }
    }

    /** And is answered from the base catalog rather than refused. */
    @Test
    void aLanguageWithNoCatalogIsAnsweredFromTheBase() {
        Locale french = Messages.resolveLocale("fr", null);

        assertEquals(Messages.get("cli.lang.tag", Locale.ENGLISH, "x"),
                Messages.get("cli.lang.tag", french, "x"));
    }

    /**
     * The whole tag, not the part in front of what went wrong. {@code en-!!} is the case that says
     * this: a check that asked whether a language came out of the tag would call it English and pass,
     * because English is exactly what the tolerant reading leaves behind.
     */
    @Test
    void aTagWithASubtagThatNamesNothingIsNotATag() {
        for (String tag : List.of("!!", "en-!!", "ja--JP", "e")) {
            assertFalse(Messages.namesALanguage(tag), tag);
        }
    }

    /** A POSIX locale writes the same thing with an underscore, and names the same language. */
    @Test
    void aPosixSpellingNamesTheSameLanguage() {
        assertTrue(Messages.namesALanguage("ja_JP"));
        assertEquals(Locale.forLanguageTag("ja-JP"), Messages.resolveLocale("ja_JP", null));
    }

    /**
     * The underscore and nothing else. What a POSIX locale carries after the territory is its
     * codeset, which is not part of naming a language — reading the tag up to it and dropping the
     * rest is the silence this is spelt out to avoid.
     */
    @Test
    void aPosixLocaleIsNotATag() {
        assertFalse(Messages.namesALanguage("ja_JP.UTF-8"));
    }

    // --- which of the two named it ------------------------------------------------------------------

    @Test
    void theLineNamesTheLanguageWhereItWritesOne() {
        Messages.Named named = Messages.namedLanguage("en", "ja");

        assertEquals("en", named.tag());
        assertFalse(named.fromEnvironment(), "the line wrote it");
    }

    @Test
    void theEnvironmentNamesItWhereTheLineDoesNot() {
        Messages.Named named = Messages.namedLanguage(null, "ja");

        assertEquals("ja", named.tag());
        assertTrue(named.fromEnvironment(), "the environment set it");
    }

    @Test
    void nothingNamesALanguageWhereNeitherWritesOne() {
        assertNull(Messages.namedLanguage(null, null));
        assertNull(Messages.namedLanguage("", "  "), "blank is not a language named");
    }

    /**
     * Only what the precedence chose. A caller holding the value that lost to being a tag would be
     * stating that every language anything on this machine names has to be well formed, which is a
     * different rule from the one that says which of them is read — and would leave a reader whose
     * shell exports something malformed unable to name a language at all.
     */
    @Test
    void theValueThatLostThePrecedenceIsNotHeldToAnything() {
        Messages.Named named = Messages.namedLanguage("en", "!!");

        assertEquals("en", named.tag());
        assertTrue(Messages.namesALanguage(named.tag()));
    }
}
