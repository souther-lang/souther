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
 * {@link Messages#BASE_LANGUAGE}: the language the schema's descriptions are written in, and what a
 * consumer written against an earlier document matches on.
 *
 * @param rendering what each source is called and how it is laid out
 * @param language  the language the prose of the page is written in
 */
record Page(SourceRendering rendering, Locale language) {

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

    /** This page with its prose in the base language, which is what two lines are told apart in. */
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

    /**
     * What tells {@code message} apart from another line of prose, and orders it among them.
     *
     * <p>Its wording in the base language: see {@link #IN_THE_BASE_WORDING}.
     */
    static String sameness(Message message) {
        return Messages.render(message, Messages.BASE_LANGUAGE);
    }
}
