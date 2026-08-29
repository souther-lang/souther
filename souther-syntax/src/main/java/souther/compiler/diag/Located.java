package souther.compiler.diag;

import souther.compiler.source.SourceId;

import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;
import java.util.Objects;

/**
 * A diagnostic and what the caller holding the files answers for it.
 *
 * <p>{@link ReportContext} is that answer, and it is two questions rather than one. This used to
 * carry a single source called "the source the primary region is in", which the region already said
 * wherever it said anything — and which was the only answer there was for a report that pointed at
 * nothing. Both readings lived in one field, so the field was empty for half the reports that had a
 * file and set for every report that had none.
 *
 * <p>Not "the file this diagnostic is in". A label says which source it is in itself
 * ({@link DiagnosticPlace}), and a diagnostic said at more than one source is read from each of them
 * in turn ({@link DiagnosticView}) — so a caller holding one of these for a file other than the one
 * the report points at is not holding a mistake.
 *
 * @param diagnostic what was found
 * @param context what the caller says: which file it is listing this under, and which text it is
 *        reading
 */
public record Located(Diagnostic diagnostic, ReportContext context) {

    public Located {
        Objects.requireNonNull(diagnostic, "something was found");
        Objects.requireNonNull(context, "a caller showing a report answers for it");
    }

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
