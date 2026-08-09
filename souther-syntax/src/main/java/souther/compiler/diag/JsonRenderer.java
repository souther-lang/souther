package souther.compiler.diag;


import tools.jackson.databind.json.JsonMapper;

import souther.compiler.diag.msg.MessageValues;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Locale;
import java.util.Map;
import java.util.Objects;

/**
 * Renders a diagnostic as a single JSON object for tools and agents. {@code code} and the type
 * strings are locale-independent (the stable identity); {@code message}, {@code hints}, and
 * secondary {@code label}s follow the selected locale.
 *
 * <p>A secondary in another file carries that file's {@code file}, which means what the top-level
 * one does — the name a reader opens. The compiler's own id for a source is not written: it is a
 * position in the list the caller handed over on the command line and a document URI in an editor,
 * so it names nothing a tool could hold on to.
 */
public final class JsonRenderer implements DiagnosticRenderer {

    private static final JsonMapper JSON = JsonMapper.builder().build();

    @Override
    public String render(Located located, SourceContextResolver sources, Locale locale) {
        Diagnostic d = located.diagnostic();
        String own = located.primarySourceId();
        DiagnosticView view = DiagnosticView.of(d, own, own);
        SourceContext anchorSource = sources.sourceOf(view.anchor().sourceId());
        Map<String, Object> obj = new LinkedHashMap<>();
        obj.put("severity", d.severity().name().toLowerCase(Locale.ROOT));
        if (d.code() != null) {
            obj.put("code", d.code());
        }
        if (anchorSource != null && anchorSource.fileName() != null) {
            obj.put("file", anchorSource.fileName());
        }
        if (view.anchor().region() != null) {
            obj.put("region", region(view.anchor().region()));
        }
        if (!view.others().isEmpty()) {
            List<Object> secs = new ArrayList<>();
            for (Spot other : view.others()) {
                Map<String, Object> s = new LinkedHashMap<>();
                if (!Objects.equals(other.sourceId(), view.anchor().sourceId())) {
                    SourceContext src = sources.sourceOf(other.sourceId());
                    if (src != null && src.fileName() != null) {
                        s.put("file", src.fileName());
                    }
                }
                s.put("region", region(other.region()));
                s.put("label", Messages.get(other.labelKey(), locale, other.labelArgs()));
                secs.add(s);
            }
            obj.put("secondary", secs);
        }
        obj.put("message", DiagnosticRenderer.body(d, locale));
        if (d.said() != null) {
            // The values the message is about, by the names its entry writes them under. A tool
            // reads `clause` or `field` rather than looking for it in a sentence, and reads it in
            // whatever language the sentence came out in: the names are the message's, not the
            // catalog's, and each value is written as the text it renders as, so what a component's
            // Java type is stays a fact about the compiler rather than part of this interface.
            Map<String, Object> values = new LinkedHashMap<>();
            MessageValues.of(d.said()).forEach((name, value) ->
                    values.put(name, String.valueOf(value)));
            obj.put("values", values);
        }
        if (d.diff() != null) {
            obj.put("actualType", d.diff().actualType());
            obj.put("expectedType", d.diff().expectedType());
        }
        List<String> hints = new ArrayList<>();
        for (Note note : d.notes()) {
            hints.add(note.said() != null ? Messages.render(note.said(), locale)
                            : Messages.get(note.messageKey(), locale, note.args()));
        }
        if (!hints.isEmpty()) {
            obj.put("hints", hints);
        }
        if (d.suggestion() != null) {
            obj.put("suggestion", d.suggestion());
        }
        return JSON.writeValueAsString(obj);
    }

    private Map<String, Object> region(Region region) {
        SourcePos s = region.start();
        SourcePos e = region.end();
        Map<String, Object> r = new LinkedHashMap<>();
        r.put("startLine", s.line());
        r.put("startCol", s.column());
        r.put("endLine", e.line());
        r.put("endCol", e.column());
        return r;
    }
}
