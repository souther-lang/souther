package souther.compiler.observe;

import souther.compiler.diag.Diagnostic;

import java.util.List;

/**
 * What evaluating a source's rows turned up: the diagnostics it reports, the observation each row
 * left, and what stopped it from observing.
 *
 * <p>Beside what it is made of, and not in the package that produced it. Nothing here names how the
 * rows were run: a diagnostic, an outcome per row, and what stopped the observing are what the
 * language asked about, so a caller reading them does not compile against whatever ran them.
 *
 * <p>Not named {@code Result} because {@code net.unit8.raoh.Result} is what a decoder answers with
 * here, and taking that spelling would take it away from it.
 */
public record Observations(List<Diagnostic> failures, List<RowOutcome> rows,
                           List<Incompleteness> incompleteness) {

    public static final Observations NONE = new Observations(List.of(), List.of(), List.of());

    public Observations {
        failures = List.copyOf(failures);
        rows = List.copyOf(rows);
        incompleteness = List.copyOf(incompleteness);
    }
}
