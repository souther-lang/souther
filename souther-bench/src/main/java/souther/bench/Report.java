package souther.bench;

import java.io.PrintStream;
import java.util.Locale;

/**
 * Where the numbers go. Every line is printed as it is measured rather than gathered and printed at
 * the end, so a run that is interrupted still shows what it had reached — a scale measurement at 200
 * modules takes long enough that this matters.
 *
 * <p>The formatting is fixed-width and the locale is fixed with it: these lines are read side by
 * side against a run taken from another revision, and a decimal comma would make two runs of the
 * same code look different.
 */
final class Report {

    private final PrintStream out;

    Report(PrintStream out) {
        this.out = out;
    }

    void line(String format, Object... args) {
        out.println(String.format(Locale.ROOT, format, args));
    }

    void blank() {
        out.println();
    }
}
