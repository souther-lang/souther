package souther.compiler.query;

import souther.compiler.diag.CompileException;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * What a {@link Key} answers: a value, or nothing, and whatever the attempt had to report.
 *
 * <p>Nothing throws to report. A question the compiler cannot answer — a name that denotes nothing,
 * a module whose type check failed — comes back absent, carrying the reports that say why, and a
 * key that asked it sees the absence and decides for itself whether it can still answer. That is
 * what lets one set of queries serve both a batch compile, which stops at the first error, and an
 * editor, which wants every module's errors at once: the difference is what the caller does with
 * what it collected, not which code ran.
 *
 * <p>An absent answer is not the same as an error. A warning rides on a present answer, and a key
 * may be absent with nothing to say, because something it read was absent and has already reported.
 *
 * @param value the answer, or {@code null} when the question could not be answered
 * @param reports what this attempt found, errors and warnings alike
 */
public record Answer<T>(T value, List<Report> reports) {

    public Answer {
        reports = List.copyOf(reports);
    }

    public static <T> Answer<T> of(T value) {
        return new Answer<>(value, List.of());
    }

    public static <T> Answer<T> of(T value, List<Report> reports) {
        return new Answer<>(value, reports);
    }

    public static <T> Answer<T> absent() {
        return new Answer<>(null, List.of());
    }

    public static <T> Answer<T> absent(Report... reports) {
        return new Answer<>(null, Arrays.asList(reports));
    }

    public static <T> Answer<T> absent(List<Report> reports) {
        return new Answer<>(null, reports);
    }

    /** The absent answer for a pass that threw — the bridge for a pass that has not stopped
     * throwing yet. */
    public static <T> Answer<T> absent(CompileException e) {
        return new Answer<>(null, Report.of(e));
    }

    /** Whether the question was answered. A caller that reads {@link #value} without asking this is
     * saying the absence cannot happen; where it can, ask. */
    public boolean present() {
        return value != null;
    }

    /** Whether anything this answer carries is an error. A present answer may still have one — a
     * pass that recovered and went on. */
    public boolean hasError() {
        return reports.stream().anyMatch(Report::isError);
    }

    /** This answer's reports followed by {@code more} — for a key that says something of its own on
     * top of what it read. */
    public List<Report> and(List<Report> more) {
        if (more.isEmpty()) {
            return reports;
        }
        List<Report> all = new ArrayList<>(reports);
        all.addAll(more);
        return List.copyOf(all);
    }

    /** The same reports with a different value — for a key that answers from what it read. */
    public <U> Answer<U> with(U value) {
        return new Answer<>(value, reports);
    }
}
