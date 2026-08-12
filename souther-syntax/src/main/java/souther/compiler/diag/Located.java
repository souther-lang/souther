package souther.compiler.diag;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * A diagnostic and which of the sources a compile was handed its primary region is in. A
 * {@link Diagnostic} says where in a file it is; which file that is belongs to the compile, not to
 * the diagnostic, so it is carried alongside.
 *
 * <p>Only the primary region. A secondary may name a source of its own
 * ({@link LabeledRegion#sourceId()}), and a diagnostic said at more than one source is read from
 * each of them in turn ({@link DiagnosticView}) — so this is not "the file this diagnostic is in",
 * and a caller holding one for a file other than this is not holding a mistake.
 *
 * @param diagnostic what was found
 * @param primarySourceId the source the primary region is in, or null when it names none — which
 *        covers a single-source compile, where the caller knows the file it handed over
 */
public record Located(Diagnostic diagnostic, String primarySourceId) {

    /** The id a diagnostic that names no source carries. */
    public static final String NO_SOURCE = null;

    /** What was found, without where — for a caller reading what a compile says rather than
     * deciding which file to put a marker in. */
    public static List<Diagnostic> diagnosticsOf(List<Located> located) {
        return located.stream().map(Located::diagnostic).toList();
    }

    /** Every source's diagnostics, without where each is anchored. */
    public static Map<String, List<Diagnostic>> diagnosticsOf(Map<String, List<Located>> bySource) {
        Map<String, List<Diagnostic>> plain = new LinkedHashMap<>();
        bySource.forEach((id, located) -> plain.put(id, diagnosticsOf(located)));
        return plain;
    }
}
