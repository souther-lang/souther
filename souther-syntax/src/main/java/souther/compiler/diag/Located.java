package souther.compiler.diag;

import souther.compiler.source.SourceId;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

/**
 * A diagnostic and which of the sources a compile was handed its primary region is in. A
 * {@link Diagnostic} says where in a file it is; which file that is belongs to the compile, not to
 * the diagnostic, so it is carried alongside.
 *
 * <p>Only the primary region. A secondary says which source it is in itself
 * ({@link DiagnosticPlace}), and a diagnostic said at more than one source is read from each of them
 * in turn ({@link DiagnosticView}) — so this is not "the file this diagnostic is in", and a caller
 * holding one for a file other than this is not holding a mistake.
 *
 * @param diagnostic what was found
 * @param primarySourceId the source the primary region is in, or null when nothing says: a
 *        position the compiler synthesized, and a report a compile could pin on no source of its
 *        own. A compile of one source is not one of those — it names that source like any other
 */
public record Located(Diagnostic diagnostic, SourceId primarySourceId) {

    /** The id a diagnostic that names no source carries. */
    public static final SourceId NO_SOURCE = null;

    /** What was found, without where — for a caller reading what a compile says rather than
     * deciding which file to put a marker in. */
    public static List<Diagnostic> diagnosticsOf(List<Located> located) {
        return located.stream().map(Located::diagnostic).toList();
    }

    /** Every source's diagnostics, without where each is anchored. */
    public static Map<SourceId, List<Diagnostic>> diagnosticsOf(Map<SourceId, List<Located>> bySource) {
        Map<SourceId, List<Diagnostic>> plain = new LinkedHashMap<>();
        bySource.forEach((id, located) -> plain.put(id, diagnosticsOf(located)));
        return plain;
    }
}
