package souther.compiler.report;

import souther.compiler.diag.Messages;
import souther.compiler.diag.SourceRendering;
import souther.compiler.diag.msg.Message;

import java.util.Comparator;
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
 * <p>A document for a machine is not written against this. It writes the same strings whatever
 * language was named, because a consumer parses them, and where it says a sentence it says it in
 * {@link #DOCUMENT_LANGUAGE}.
 *
 * @param rendering what each source is called and how it is laid out
 * @param language  the language the prose of the page is written in
 */
record Page(SourceRendering rendering, Locale language) {

    /**
     * The language a document says a sentence in, whichever one the reader named.
     *
     * <p>English, because it is what the schema's descriptions are written in and what a consumer
     * written against an earlier document matches on. It is also the language the catalog is
     * written from, so it is the one every other entry is a translation of.
     */
    static final Locale DOCUMENT_LANGUAGE = Locale.ENGLISH;

    /**
     * Two prose lines are the same line, and in which order prose lines are said, as the catalog's
     * base language words them.
     *
     * <p>Not as the reader's language words them. Two things a translation happens to word alike
     * are still two things, and an order taken from a translation's wording would put one model's
     * lines in a different order in each language — so the lines a page says, and the order it
     * says them in, are the same whichever language it is written in.
     */
    static final Comparator<Message> IN_THE_BASE_WORDING = Comparator.comparing(Page::sameness);

    Page {
        Objects.requireNonNull(rendering, "a page names its sources");
        Objects.requireNonNull(language, "a page is written in a language");
    }

    /** {@code message} in the language of this page. */
    String say(Message message) {
        return Messages.render(message, language);
    }

    /**
     * What tells {@code message} apart from another line of prose, and orders it among them.
     *
     * <p>Its wording in the base language: see {@link #IN_THE_BASE_WORDING}.
     */
    static String sameness(Message message) {
        return Messages.render(message, DOCUMENT_LANGUAGE);
    }
}
