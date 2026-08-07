package souther.compiler.diag;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

/** Turns a {@link Diagnostic} into text: {@link HumanRenderer} for people, {@link JsonRenderer} for
 * tools. The source snippets come from {@code sources}, which answers null for a source that is
 * unavailable (e.g. a file that cannot be read); the renderer then omits the quoted line. */
public interface DiagnosticRenderer {

    /**
     * One diagnostic, quoted from the files its regions are in. {@code located} carries the source
     * the primary region is in; a secondary that names one of its own is quoted from that.
     */
    String render(Located located, SourceContextResolver sources, Locale locale);

    /**
     * One diagnostic written wholly in one file, quoted from {@code src}. Everything it points at is
     * in that file, so there is nothing to resolve and nothing to name.
     */
    default String render(Diagnostic d, SourceContext src, Locale locale) {
        return render(new Located(d, Located.NO_SOURCE), id -> src, locale);
    }

    /**
     * Renders each of {@code located}, one string per diagnostic — never one string for the list, so
     * a JSON caller prints one object per line rather than an array.
     *
     * <p>One string per diagnostic and not per file: a problem written in two of them is one
     * diagnostic here, quoted at both of the places it is written. What is said twice in an editor,
     * which puts a marker in each file, is said once on a terminal, which is read top to bottom.
     */
    static List<String> renderAll(List<Located> located, SourceContextResolver sources,
                                  DiagnosticRenderer renderer, Locale locale) {
        List<String> rendered = new ArrayList<>(located.size());
        for (Located one : located) {
            rendered.add(renderer.render(one, sources, locale));
        }
        return List.copyOf(rendered);
    }

    /**
     * The body a {@code CompileException} builds its {@code getMessage()} from — that text with
     * the position and the code put in front of it.
     *
     * <p>There is no language to pass. An adapter prints that text only for an exception carrying no
     * diagnostic, and the two sites that build this always supply one, so nothing rendering for a
     * reader ever reads it; what reads it is {@code getMessage()} itself, in a test or an embedding
     * caller. What it has to do is not change when the language a reader is answered in is decided
     * again — a different requirement from being English, and the reason the caller does not get to
     * choose one. English is what this text is.
     */
    static String legacyBody(Diagnostic d) {
        return body(d, Locale.ENGLISH);
    }

    /** The message body, from the catalog key or the compatibility literal. */
    static String body(Diagnostic d, Locale locale) {
        java.util.Objects.requireNonNull(locale, Messages.NEEDS_A_LANGUAGE);
        if (d.literalMessage() != null) {
            return d.literalMessage();
        }
        if (d.messageKey() != null) {
            return Messages.get(d.messageKey(), locale, d.args());
        }
        return "";
    }
}
