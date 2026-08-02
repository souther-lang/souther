package souther.compiler.diag;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;
import java.util.function.IntFunction;

/** Turns a {@link Diagnostic} into text: {@link HumanRenderer} for people, {@link JsonRenderer} for
 * tools. The source snippet comes from {@code src}, which may be null when the source is unavailable
 * (e.g. a multi-file build); the renderer then omits the quoted line. */
public interface DiagnosticRenderer {

    String render(Diagnostic d, SourceContext src, Locale locale);

    /**
     * Renders each of {@code located}, one string per diagnostic — never one string for the list, so
     * a JSON caller prints one object per line rather than an array.
     *
     * <p>Each diagnostic quotes its own file: a compile reporting several modules at once has one per
     * module, and they do not share a source. {@code sourceAt} maps a
     * {@link Located#sourceIndex()} to the text to quote, and is asked about
     * {@link Located#NO_SOURCE} as well — what an unnamed source means is the caller's to say, since
     * a single-source compile names none and yet has exactly one file to quote. Returning null there
     * (or for a file that cannot be read) leaves the snippet out rather than quoting the wrong line.
     */
    static List<String> renderAll(List<Located> located, IntFunction<SourceContext> sourceAt,
                                  DiagnosticRenderer renderer, Locale locale) {
        List<String> rendered = new ArrayList<>(located.size());
        for (Located one : located) {
            rendered.add(renderer.render(one.diagnostic(), sourceAt.apply(one.sourceIndex()), locale));
        }
        return List.copyOf(rendered);
    }

    /** The message body, from the catalog key or the compatibility literal. */
    static String body(Diagnostic d, Locale locale) {
        if (d.literalMessage() != null) {
            return d.literalMessage();
        }
        if (d.messageKey() != null) {
            return Messages.get(d.messageKey(), locale, d.args());
        }
        return "";
    }
}
