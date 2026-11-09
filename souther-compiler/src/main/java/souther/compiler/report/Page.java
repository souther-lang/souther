package souther.compiler.report;

import souther.compiler.diag.Messages;
import souther.compiler.diag.SourceRendering;
import souther.compiler.diag.msg.Message;

import java.util.Locale;
import java.util.Objects;

/**
 * What a page for a person is written against: what to call each source, and which language the
 * person reads.
 *
 * <p>Both are decided when the page is written and not when the report was worked out, which is why
 * neither is a part of the report. The sources are named for the set in front of this reader; the
 * language is the one this reader named, resolved once by whoever answers them — the command line,
 * the editor — and never read again from the environment here.
 *
 * <p>The language is how a line is worded and nothing else. Which lines a page says, how many of a
 * kind it counts, and in which order, are decided over what each line says — the message — before
 * any language words it ({@link souther.compiler.diag.msg.MessageOrder}). Decided over words, two
 * statements a language happens to word alike would be said once, and the same model would be read
 * out in a different order in each language and after each rewording of the catalog.
 *
 * <p>A document for a machine is not written against this. It writes the same strings whatever
 * language was named, because a consumer parses them, and where it says a sentence it says it in
 * {@link Messages#BASE_LANGUAGE}: the language the schema's descriptions are written in, and what a
 * consumer written against an earlier document matches on.
 *
 * @param rendering what each source is called and how it is laid out
 * @param language  the language the prose of the page is written in
 */
record Page(SourceRendering rendering, Locale language) {

    Page {
        Objects.requireNonNull(rendering, "a page names its sources");
        Objects.requireNonNull(language, "a page is written in a language");
    }

    /**
     * This page with its prose in the base language, for words that are source rather than prose:
     * the name a row is given is what an author pastes, and is the same whichever language the
     * comments around it are in.
     */
    Page base() {
        return language.equals(Messages.BASE_LANGUAGE)
                ? this : new Page(rendering, Messages.BASE_LANGUAGE);
    }

    /** {@code message} as a document writes it, which is in {@link Messages#BASE_LANGUAGE}. */
    static String inTheDocument(Message message) {
        return Messages.render(message, Messages.BASE_LANGUAGE);
    }

    /** {@code message} in the language of this page. */
    String say(Message message) {
        return Messages.render(message, language);
    }
}
