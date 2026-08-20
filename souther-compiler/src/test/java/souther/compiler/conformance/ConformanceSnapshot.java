package souther.compiler.conformance;

import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticPlace;
import souther.compiler.diag.Located;
import souther.compiler.diag.Primary;
import souther.compiler.diag.QuotedFrom;
import souther.compiler.diag.Region;
import souther.compiler.diag.SourceNameResolver;
import souther.compiler.diag.SourceProvenance;
import souther.compiler.report.AdequacyReport;

import java.util.ArrayList;
import java.util.List;

/**
 * The two documents a corpus is held against, written the same way every time.
 *
 * <p>Split in two because they churn for different reasons. What the compiler answered about a
 * model changes when the compiler's answers change, which is the whole point of keeping it; what a
 * diagnostic says changes when someone rewords a message, which is held by the test that owns that
 * rule and would otherwise rewrite the corpus every time.
 */
final class ConformanceSnapshot {

    /** Stood in for the version, which moves for reasons unrelated to what the compiler answered. */
    private static final String VERSION_PLACEHOLDER = "<version>";

    private ConformanceSnapshot() {
    }

    /**
     * What this compiler answered about the corpus, as the report writes it.
     *
     * <p>The whole document rather than a summary of it. Whether the rows are adequate is one bit,
     * and which class was covered and which branch ran is underneath — a change that leaves the bit
     * alone while swapping what it covers shows nowhere else.
     */
    static String report(ConformanceCorpus.Analysed analysed) {
        AdequacyReport report = AdequacyReport.of(analysed.compilation());
        SourceNameResolver names = analysed.corpus().names();
        return report.json(names).replace("\"" + report.compilerVersion() + "\"",
                "\"" + VERSION_PLACEHOLDER + "\"") + System.lineSeparator();
    }

    /**
     * Everything the compiler said about the corpus, one line each.
     *
     * <p>Without the message. Where each of them is written is what a reader of a difference needs
     * to go and look, and it is the half that does not move when a sentence is rewritten.
     *
     * <p>Where a report points is asked case by case rather than through one accessor answering
     * "the region, if there is one" — {@link Primary} has four cases and three of them are not a
     * region, and a renderer that read them as one absence would write the same line for a report
     * about the standard library and one about nothing at all.
     */
    static String diagnostics(ConformanceCorpus.Analysed analysed) {
        SourceNameResolver names = analysed.corpus().names();
        List<String> lines = new ArrayList<>();
        for (Located located : analysed.said()) {
            Diagnostic diagnostic = located.diagnostic();
            String code = diagnostic.code() == null ? "<uncoded>" : diagnostic.code();
            lines.add(diagnostic.severity().name().toLowerCase() + " " + code + " "
                    + where(diagnostic.primary(), names));
        }
        return lines.isEmpty() ? "" : String.join(System.lineSeparator(), lines)
                + System.lineSeparator();
    }

    private static String where(Primary primary, SourceNameResolver names) {
        return switch (primary) {
            case Primary.InSource(DiagnosticPlace.InSource place) -> at(place.region(), names);
            case Primary.InAnUnnamedText(var unnamed) -> "in an unnamed text "
                    + line(unnamed.region());
            case Primary.Unavailable(SourceProvenance from) -> "in " + from;
            case Primary.Nowhere() -> "nowhere";
        };
    }

    private static String at(Region region, SourceNameResolver names) {
        // A place a reader is sent to names the source it is in, which `DiagnosticPlace.InSource`
        // refuses to be built without — so the one case here is the only one there is.
        String file = region.start().quotedFrom()
                instanceof QuotedFrom.ASourceThisCompileHolds(var source)
                ? names.nameOf(source)
                : "<unnamed>";
        return (file == null ? "<unnamed>" : file) + ":" + line(region);
    }

    private static String line(Region region) {
        return region.start().line() + ":" + region.start().column();
    }
}
