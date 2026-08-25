package souther.compiler.diag;

import java.util.List;

/**
 * The one-line text a compile of failing examples is carried out on.
 *
 * <p>Not what a reader is shown. The CLI, the annotation processor and the LSP all render the
 * diagnostics the exception carries; what this is for is the body {@code getMessage()} is built
 * from, which a caller holding the exception reads and no surface prints. It takes no language for
 * the same reason {@link DiagnosticRenderer#legacyBody} does not.
 *
 * <p>Here rather than beside the thing that runs the rows. How several failures are gathered into
 * one sentence is a decision about a report, and it stayed in the example subsystem only because
 * that is where the failures were counted. It is not beside {@code DiagnosticRenderer} either: how
 * one diagnostic becomes a legacy body is every diagnostic's question, and how many of them make
 * "N examples do not hold" is this one's.
 */
public final class ExampleDiagnostics {

    private ExampleDiagnostics() {}

    /** The one-line form for a set of failures gathered across modules: the count, then the first
     * one's reason, matching what a single module's aggregate says. */
    public static String legacySummary(List<Diagnostic> failures) {
        Diagnostic first = failures.get(0);
        return failures.size() == 1
                ? legacyOf(first)
                : failures.size() + " examples do not hold; " + legacyOf(first);
    }

    /** A one-line message for one failing example. */
    private static String legacyOf(Diagnostic d) {
        if (d.diff() != null) {
            // JUnit order: the expected value (what the example asserts) first, then what the
            // behavior actually produced.
            return "example does not hold: expected " + d.diff().expectedType()
                    + " but was " + d.diff().actualType();
        }
        // A diff-less failure (an input fixture that could not be built, a missing fake, a
        // non-termination): render the diagnostic's own catalog message so the reason travels
        // through the annotation processor, rather than collapsing to a bare "example failed".
        return d.said() == null ? "example failed" : DiagnosticRenderer.legacyBody(d);
    }
}
