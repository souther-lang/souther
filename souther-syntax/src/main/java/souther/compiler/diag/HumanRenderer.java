package souther.compiler.diag;


import java.util.Locale;

/**
 * Renders a diagnostic Elm-style: a title bar with the error name and location, the offending source
 * line with a caret underline, then the message, any found-vs-expected type blocks, and hints. Color
 * is applied only when {@code useColor} is set (the caller decides from TTY and {@code NO_COLOR}).
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
    public String render(Diagnostic d, SourceContext src, Locale locale) {
        StringBuilder out = new StringBuilder();
        header(out, d, src, locale);
        out.append('\n');
        snippet(out, d.region(), src, d.severity() == Severity.WARNING ? YELLOW : RED);
        for (LabeledRegion sec : d.secondary()) {
            out.append('\n');
            snippet(out, sec.region(), src, CYAN);
            out.append(color(DIM, Messages.get(sec.labelKey(), locale, sec.labelArgs()))).append('\n');
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
     * The header's title. A diagnostic that names what it is about keeps that name and says its
     * severity beside it; one that names nothing is titled by its severity alone. A warning is
     * marked either way, since the code and the message read the same for both and the bar is the
     * only place the difference can be seen.
     */
    private String title(Diagnostic d, Locale locale) {
        String specific = specificTitle(d, locale);
        if (d.severity() != Severity.WARNING) {
            return specific != null ? specific : Messages.get("diag.error.title", locale);
        }
        String warning = Messages.get("diag.warning.title", locale);
        return specific != null ? specific + " (" + warning + ")" : warning;
    }

    /** What this diagnostic is about — its own title, or the one its code carries — or null when it
     *  names neither and only its severity is left to title it with. */
    private String specificTitle(Diagnostic d, Locale locale) {
        if (d.titleKey() != null && Messages.has(d.titleKey(), locale)) {
            return Messages.get(d.titleKey(), locale);
        }
        if (d.code() != null) {
            String key = d.code().toLowerCase(Locale.ROOT) + ".title";
            if (Messages.has(key, locale)) {
                return Messages.get(key, locale);
            }
        }
        return null;
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
