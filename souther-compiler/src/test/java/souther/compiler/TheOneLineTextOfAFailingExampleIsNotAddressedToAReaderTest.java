package souther.compiler;

import souther.compiler.examples.ExampleVerifier;
import souther.compiler.diag.msg.ExampleMessage;
import org.junit.jupiter.api.Test;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.Messages;

import java.util.List;
import java.util.Locale;

import static org.junit.jupiter.api.Assertions.assertEquals;
import static org.junit.jupiter.api.Assertions.assertNotEquals;

/**
 * The one-line text a failing example is thrown with is the English catalog text, and stays it.
 *
 * <p>That text is the body {@code getMessage()} is built from, under the position and code it puts
 * in front. No surface prints it — the exception carries a
 * diagnostic per failing row, and the CLI, the annotation processor and the LSP all render those —
 * so what reads it is a caller holding the exception: a test, or something embedding the compiler.
 * Which is why it is not the reader's language: there is no reader here to have one.
 *
 * <p>It was the language Souther fell back to, which is a different thing that agreed with it. When
 * that fallback was Japanese this text was Japanese, and it stopped being Japanese because the
 * fallback was decided again — not because anything decided anything about failing examples.
 */
class TheOneLineTextOfAFailingExampleIsNotAddressedToAReaderTest {

    private static final ExampleMessage.TheRowReachedAnUnreachablePoint SAID =
            new ExampleMessage.TheRowReachedAnUnreachablePoint("no branch states this");

    @Test
    void aFailingExampleSaysWhatTheEnglishCatalogSays() {
        Diagnostic failure = Diagnostic.say(SAID).nowhere().build();

        String said = ExampleVerifier.legacySummary(List.of(failure));

        assertEquals(Messages.render(SAID, Locale.ENGLISH), said);
    }

    /**
     * And the catalog answers this key in more than one language, so the assertion above is a claim
     * about which one rather than a claim two languages would both satisfy.
     */
    @Test
    void theCatalogWouldHaveSaidSomethingElseInJapanese() {
        Diagnostic failure = Diagnostic.say(SAID).nowhere().build();

        String said = ExampleVerifier.legacySummary(List.of(failure));

        assertNotEquals(Messages.render(SAID, Locale.JAPANESE), said);
    }
}
