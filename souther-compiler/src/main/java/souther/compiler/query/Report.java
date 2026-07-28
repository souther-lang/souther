package souther.compiler.query;

import souther.compiler.diag.CompileException;
import souther.compiler.diag.Diagnostic;
import souther.compiler.diag.DiagnosticRenderer;
import souther.compiler.diag.Severity;

import java.util.ArrayList;
import java.util.List;
import java.util.Locale;

/**
 * One thing a query found: the structured {@link Diagnostic} a renderer works from, and the
 * one-line English text {@link CompileException#getMessage()} has always returned for it.
 *
 * <p>The second field is here because the first cannot reproduce it. A migrated throw site builds a
 * catalog-keyed diagnostic and passes its English body separately to
 * {@link CompileException#of(Diagnostic, String)}; that body never reaches the diagnostic, and it
 * cannot be put there, because {@link DiagnosticRenderer} prefers a literal message over a catalog
 * key — every migrated site would go back to rendering English instead of the reader's locale.
 *
 * <p>So a query wrapping a pass that still throws keeps both halves, and a caller that has to throw
 * again — a batch compile stopping at the first error — raises the same exception the pass did. A
 * report built any other way has no text of its own and renders one when asked.
 *
 * @param diagnostic what was found
 * @param legacyMessage the text the pass raised it with, or null when it was not raised
 */
public record Report(Diagnostic diagnostic, String legacyMessage) {

    public boolean isError() {
        return diagnostic.severity() == Severity.ERROR;
    }

    /** A report with no raised text of its own. */
    public static Report of(Diagnostic diagnostic) {
        return new Report(diagnostic, null);
    }

    /**
     * A report carrying the English body a pass would have raised it with — for a check moved off a
     * throw and into a query, where the message a caller reads should not change because the check
     * moved.
     */
    public static Report raised(Diagnostic diagnostic, String body) {
        return new Report(diagnostic, CompileException.of(diagnostic, body).getMessage());
    }

    /** A thrown error as reports, one per diagnostic it carries. The exception's message belongs to
     * its first diagnostic; the rest never had one of their own. */
    public static List<Report> of(CompileException e) {
        List<Diagnostic> diagnostics = e.diagnostics();
        if (diagnostics.isEmpty()) {
            return List.of(new Report(Diagnostic.literal(null, null, e.getMessage()), e.getMessage()));
        }
        List<Report> reports = new ArrayList<>();
        reports.add(new Report(diagnostics.get(0), e.getMessage()));
        for (int i = 1; i < diagnostics.size(); i++) {
            reports.add(of(diagnostics.get(i)));
        }
        return List.copyOf(reports);
    }

    /** Every report of every answer, in order — for a key that passes on what it read. */
    public static List<Report> ofAll(List<? extends Answer<?>> answers) {
        List<Report> all = new ArrayList<>();
        for (Answer<?> a : answers) {
            all.addAll(a.reports());
        }
        return List.copyOf(all);
    }

    /** Only the errors among {@code reports} — what a caller that stops at the first one looks at,
     * since a warning is not a reason to stop. */
    public static List<Report> errorsIn(List<Report> reports) {
        return reports.stream().filter(Report::isError).toList();
    }

    /**
     * What makes this the same problem as another: what is wrong, said the same way, in the same
     * place.
     *
     * <p>Two questions can find one problem. A helper is checked on its own and again wherever it is
     * expanded, and both are looking at the same line of the same helper — so the author is told
     * twice about one mistake unless the two are recognised as one. Neither is wrong to have found
     * it, and neither can see the other, so it is the reading of them that settles it.
     */
    public String problem() {
        return diagnostic.code() + "|" + diagnostic.messageKey() + "|" + diagnostic.literalMessage()
                + "|" + diagnostic.severity() + "|" + diagnostic.region();
    }

    /** This report as an error to throw. One built from a raised exception throws that exception's
     * message again; one built any other way renders its own, in English, because that message has
     * always been English and a test that reads it should not move with the reader's locale. */
    public CompileException asException() {
        return legacyMessage == null
                ? CompileException.of(diagnostic, DiagnosticRenderer.body(diagnostic, Locale.ENGLISH))
                : new CompileException(diagnostic, legacyMessage);
    }
}
