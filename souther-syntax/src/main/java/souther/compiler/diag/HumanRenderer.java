package souther.compiler.diag;


import java.util.Locale;
import java.util.Objects;

/**
 * Renders a diagnostic Elm-style: a title bar with the error name and location, the offending source
 * line with a caret underline, then the message, any found-vs-expected type blocks, and hints. Color
 * is applied only when {@code useColor} is set (the caller decides from TTY and {@code NO_COLOR}).
 *
 * <p>A region in another file is quoted from that file and says where it is, so a problem written
 * in two of them reads as one block rather than as two diagnostics the reader has to pair up.
 */
public final class HumanRenderer implements DiagnosticRenderer {

    private static final int WIDTH = 60;

    private static final String RESET = "[0m";
    private static final String CYAN = "[36m";
    private static final String RED = "[31m";
    private static final String YELLOW = "[33m";
    private static final String DIM = "[2m";

    private final boolean useColor;

    public HumanRenderer(boolean useColor) {
        this.useColor = useColor;
    }

    @Override
    public String render(Located located, SourceContextResolver sources, Locale locale) {
        Diagnostic d = located.diagnostic();
        String own = located.primarySourceId();
        DiagnosticView view = DiagnosticView.of(d, own, own);
        SourceContext anchorSource = sources.sourceOf(view.anchor().sourceId());
        StringBuilder out = new StringBuilder();
        header(out, d, anchorSource, locale);
        out.append('\n');
        snippet(out, view.anchor().region(), anchorSource,
                d.severity() == Severity.WARNING ? YELLOW : RED);
        for (Spot other : view.others()) {
            out.append('\n');
            SourceContext src = sources.sourceOf(other.sourceId());
            if (!Objects.equals(other.sourceId(), view.anchor().sourceId())) {
                out.append(color(DIM, location(startOf(other.region()), src))).append('\n');
            }
            snippet(out, other.region(), src, CYAN);
            if (other.labelled()) {
                out.append(color(DIM, Messages.get(other.labelKey(), locale, other.labelArgs())))
                        .append('\n');
            }
        }
        out.append('\n').append(DiagnosticRenderer.body(d, locale)).append('\n');
        if (d.diff() != null) {
            out.append('\n');
            out.append(Messages.get("diag.diff.found", locale)).append('\n');
            out.append("    ").append(d.diff().actualType()).append('\n');
            out.append(Messages.get("diag.diff.expected", locale)).append('\n');
            out.append("    ").append(d.diff().expectedType()).append('\n');
        }
        if (d.suggestion() != null) {
            out.append(hintLabel(locale))
                    .append(Messages.get("diag.suggestion", locale, d.suggestion())).append('\n');
        }
        for (Note note : d.notes()) {
            out.append(hintLabel(locale))
                    .append(Messages.get(note.messageKey(), locale, note.args())).append('\n');
        }
        return out.toString();
    }

    private void header(StringBuilder out, Diagnostic d, SourceContext src, Locale locale) {
        String title = title(d, locale);
        String code = d.code() == null ? "" : "  " + d.code();
        String left = "-- " + title + code + " ";
        String loc = location(d.pos(), src);
        int dashes = WIDTH - left.length() - loc.length();
        StringBuilder bar = new StringBuilder(left);
        for (int i = 0; i < dashes; i++) {
            bar.append('-');
        }
        if (!loc.isEmpty()) {
            bar.append(dashes > 0 ? "" : "-").append(loc);
        }
        out.append(color(CYAN, bar.toString())).append('\n');
    }

    /**
     * The header's title: the category the diagnostic states, with its severity beside it, or the
     * severity alone when it states none. A warning is marked either way, since the code and the
     * message read the same for both and the bar is the only place the difference can be seen.
     *
     * <p>The title is not derived from the code. A code names a rule and a title names a category,
     * and one category holds many rules — deriving one from the other would put a per-code title in
     * the catalog for every rule and print the same category under a different wording each time.
     * A coded diagnostic is given its title by {@link DiagnosticCode}, before it reaches here.
     */
    private String title(Diagnostic d, Locale locale) {
        String about = d.titleKey() != null && Messages.has(d.titleKey(), locale)
                ? Messages.get(d.titleKey(), locale)
                : null;
        if (d.severity() != Severity.WARNING) {
            return about != null ? about : Messages.get("diag.error.title", locale);
        }
        String warning = Messages.get("diag.warning.title", locale);
        return about != null ? about + " (" + warning + ")" : warning;
    }

    private static SourcePos startOf(Region region) {
        return region == null ? null : region.start();
    }

    private String location(SourcePos pos, SourceContext src) {
        if (pos == null) {
            return src == null || src.fileName() == null ? "" : src.fileName();
        }
        String file = src == null || src.fileName() == null ? "" : src.fileName() + ":";
        return file + pos.line() + ":" + pos.column();
    }

    private void snippet(StringBuilder out, Region region, SourceContext src, String caretColor) {
        if (region == null || src == null) {
            return;
        }
        SourcePos start = region.start();
        String line = src.line(start.line());
        if (line == null) {
            return;
        }
        String gutter = start.line() + "| ";
        out.append(color(DIM, gutter)).append(line).append('\n');
        StringBuilder caret = new StringBuilder();
        for (int i = 0; i < gutter.length() + start.column() - 1; i++) {
            caret.append(' ');
        }
        int width = region.caretWidth();
        for (int i = 0; i < width; i++) {
            caret.append('^');
        }
        out.append(color(caretColor, caret.toString())).append('\n');
    }

    private String hintLabel(Locale locale) {
        return Messages.get("diag.hint.label", locale) + " ";
    }

    private String color(String code, String text) {
        return useColor ? code + text + RESET : text;
    }
}
